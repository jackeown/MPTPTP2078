%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:28 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  172 (1171 expanded)
%              Number of clauses        :  102 ( 291 expanded)
%              Number of leaves         :   18 ( 458 expanded)
%              Depth                    :   22
%              Number of atoms          : 1022 (14869 expanded)
%              Number of equality atoms :  385 (3557 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f37])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f38,f48,f47,f46,f45,f44,f43])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v1_funct_1(sK5) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f33])).

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
    inference(nnf_transformation,[],[f34])).

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

fof(f65,plain,(
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

fof(f88,plain,(
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
    inference(equality_resolution,[],[f65])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f35])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f82,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f73,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f40,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,(
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

fof(f87,plain,(
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
    inference(equality_resolution,[],[f66])).

fof(f71,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1215,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1231,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2394,plain,
    ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_1215,c_1231])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1218,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1226,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3076,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1226])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3210,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3076,c_42])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1221,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3075,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_1226])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3198,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3075,c_45])).

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
    inference(cnf_transformation,[],[f88])).

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
    inference(cnf_transformation,[],[f68])).

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
    inference(cnf_transformation,[],[f69])).

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
    inference(cnf_transformation,[],[f70])).

cnf(c_184,plain,
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

cnf(c_185,plain,
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
    inference(renaming,[status(thm)],[c_184])).

cnf(c_1209,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_185])).

cnf(c_3790,plain,
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
    inference(superposition,[status(thm)],[c_3198,c_1209])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_39,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6542,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3790,c_36,c_39,c_45,c_46,c_47])).

cnf(c_6543,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
    | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6542])).

cnf(c_6549,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3210,c_6543])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1315,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1316,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1315])).

cnf(c_6584,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6549,c_37,c_42,c_43,c_44,c_1316])).

cnf(c_6585,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6584])).

cnf(c_6590,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_6585])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_253,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_466,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_467,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_469,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_467,c_32,c_30])).

cnf(c_506,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_253,c_469])).

cnf(c_507,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1227,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2216,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_1227])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1233,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1228,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1232,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2439,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1232])).

cnf(c_3920,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1233,c_2439])).

cnf(c_3928,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2216,c_3920])).

cnf(c_6591,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6590,c_507,c_3928])).

cnf(c_6592,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6591,c_2394])).

cnf(c_2217,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1218,c_1227])).

cnf(c_3929,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2217,c_3920])).

cnf(c_6593,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6592,c_507,c_3929])).

cnf(c_6594,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6593])).

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
    inference(cnf_transformation,[],[f87])).

cnf(c_191,plain,
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

cnf(c_192,plain,
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
    inference(renaming,[status(thm)],[c_191])).

cnf(c_1208,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_3023,plain,
    ( k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),sK3) = X3
    | k2_partfun1(sK3,X1,X3,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK3))
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK3,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2394,c_1208])).

cnf(c_3027,plain,
    ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK3)) != k2_partfun1(sK3,X1,X3,k3_xboole_0(X0,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),sK3) = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK3,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3023,c_2394])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4225,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_2(X3,sK3,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),sK3) = X3
    | k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK3)) != k2_partfun1(sK3,X1,X3,k3_xboole_0(X0,sK3))
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3027,c_35,c_39,c_40])).

cnf(c_4226,plain,
    ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK3)) != k2_partfun1(sK3,X1,X3,k3_xboole_0(X0,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),sK3) = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,sK3,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4225])).

cnf(c_4233,plain,
    ( k2_partfun1(X0,sK1,X1,k3_xboole_0(X0,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3198,c_4226])).

cnf(c_4600,plain,
    ( v1_xboole_0(X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | k2_partfun1(X0,sK1,X1,k3_xboole_0(X0,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4233,c_36,c_45,c_46,c_47])).

cnf(c_4601,plain,
    ( k2_partfun1(X0,sK1,X1,k3_xboole_0(X0,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) = sK5
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4600])).

cnf(c_4607,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3210,c_4601])).

cnf(c_4610,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4607,c_507,c_3928,c_3929])).

cnf(c_4611,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4610])).

cnf(c_21,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2869,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2394,c_21])).

cnf(c_2870,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2869,c_507])).

cnf(c_3241,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2870,c_3198,c_3210])).

cnf(c_3968,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3928,c_3241])).

cnf(c_3969,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3968,c_3929])).

cnf(c_3970,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_3969])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6594,c_4611,c_3970,c_44,c_43,c_42,c_40,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.94/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.94/0.99  
% 3.94/0.99  ------  iProver source info
% 3.94/0.99  
% 3.94/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.94/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.94/0.99  git: non_committed_changes: false
% 3.94/0.99  git: last_make_outside_of_git: false
% 3.94/0.99  
% 3.94/0.99  ------ 
% 3.94/0.99  
% 3.94/0.99  ------ Input Options
% 3.94/0.99  
% 3.94/0.99  --out_options                           all
% 3.94/0.99  --tptp_safe_out                         true
% 3.94/0.99  --problem_path                          ""
% 3.94/0.99  --include_path                          ""
% 3.94/0.99  --clausifier                            res/vclausify_rel
% 3.94/0.99  --clausifier_options                    ""
% 3.94/0.99  --stdin                                 false
% 3.94/0.99  --stats_out                             all
% 3.94/0.99  
% 3.94/0.99  ------ General Options
% 3.94/0.99  
% 3.94/0.99  --fof                                   false
% 3.94/0.99  --time_out_real                         305.
% 3.94/0.99  --time_out_virtual                      -1.
% 3.94/0.99  --symbol_type_check                     false
% 3.94/0.99  --clausify_out                          false
% 3.94/0.99  --sig_cnt_out                           false
% 3.94/0.99  --trig_cnt_out                          false
% 3.94/0.99  --trig_cnt_out_tolerance                1.
% 3.94/0.99  --trig_cnt_out_sk_spl                   false
% 3.94/0.99  --abstr_cl_out                          false
% 3.94/0.99  
% 3.94/0.99  ------ Global Options
% 3.94/0.99  
% 3.94/0.99  --schedule                              default
% 3.94/0.99  --add_important_lit                     false
% 3.94/0.99  --prop_solver_per_cl                    1000
% 3.94/0.99  --min_unsat_core                        false
% 3.94/0.99  --soft_assumptions                      false
% 3.94/0.99  --soft_lemma_size                       3
% 3.94/0.99  --prop_impl_unit_size                   0
% 3.94/0.99  --prop_impl_unit                        []
% 3.94/0.99  --share_sel_clauses                     true
% 3.94/0.99  --reset_solvers                         false
% 3.94/0.99  --bc_imp_inh                            [conj_cone]
% 3.94/0.99  --conj_cone_tolerance                   3.
% 3.94/0.99  --extra_neg_conj                        none
% 3.94/0.99  --large_theory_mode                     true
% 3.94/0.99  --prolific_symb_bound                   200
% 3.94/0.99  --lt_threshold                          2000
% 3.94/0.99  --clause_weak_htbl                      true
% 3.94/0.99  --gc_record_bc_elim                     false
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing Options
% 3.94/0.99  
% 3.94/0.99  --preprocessing_flag                    true
% 3.94/0.99  --time_out_prep_mult                    0.1
% 3.94/0.99  --splitting_mode                        input
% 3.94/0.99  --splitting_grd                         true
% 3.94/0.99  --splitting_cvd                         false
% 3.94/0.99  --splitting_cvd_svl                     false
% 3.94/0.99  --splitting_nvd                         32
% 3.94/0.99  --sub_typing                            true
% 3.94/0.99  --prep_gs_sim                           true
% 3.94/0.99  --prep_unflatten                        true
% 3.94/0.99  --prep_res_sim                          true
% 3.94/0.99  --prep_upred                            true
% 3.94/0.99  --prep_sem_filter                       exhaustive
% 3.94/0.99  --prep_sem_filter_out                   false
% 3.94/0.99  --pred_elim                             true
% 3.94/0.99  --res_sim_input                         true
% 3.94/0.99  --eq_ax_congr_red                       true
% 3.94/0.99  --pure_diseq_elim                       true
% 3.94/0.99  --brand_transform                       false
% 3.94/0.99  --non_eq_to_eq                          false
% 3.94/0.99  --prep_def_merge                        true
% 3.94/0.99  --prep_def_merge_prop_impl              false
% 3.94/0.99  --prep_def_merge_mbd                    true
% 3.94/0.99  --prep_def_merge_tr_red                 false
% 3.94/0.99  --prep_def_merge_tr_cl                  false
% 3.94/0.99  --smt_preprocessing                     true
% 3.94/0.99  --smt_ac_axioms                         fast
% 3.94/0.99  --preprocessed_out                      false
% 3.94/0.99  --preprocessed_stats                    false
% 3.94/0.99  
% 3.94/0.99  ------ Abstraction refinement Options
% 3.94/0.99  
% 3.94/0.99  --abstr_ref                             []
% 3.94/0.99  --abstr_ref_prep                        false
% 3.94/0.99  --abstr_ref_until_sat                   false
% 3.94/0.99  --abstr_ref_sig_restrict                funpre
% 3.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.94/0.99  --abstr_ref_under                       []
% 3.94/0.99  
% 3.94/0.99  ------ SAT Options
% 3.94/0.99  
% 3.94/0.99  --sat_mode                              false
% 3.94/0.99  --sat_fm_restart_options                ""
% 3.94/0.99  --sat_gr_def                            false
% 3.94/0.99  --sat_epr_types                         true
% 3.94/0.99  --sat_non_cyclic_types                  false
% 3.94/0.99  --sat_finite_models                     false
% 3.94/0.99  --sat_fm_lemmas                         false
% 3.94/0.99  --sat_fm_prep                           false
% 3.94/0.99  --sat_fm_uc_incr                        true
% 3.94/0.99  --sat_out_model                         small
% 3.94/0.99  --sat_out_clauses                       false
% 3.94/0.99  
% 3.94/0.99  ------ QBF Options
% 3.94/0.99  
% 3.94/0.99  --qbf_mode                              false
% 3.94/0.99  --qbf_elim_univ                         false
% 3.94/0.99  --qbf_dom_inst                          none
% 3.94/0.99  --qbf_dom_pre_inst                      false
% 3.94/0.99  --qbf_sk_in                             false
% 3.94/0.99  --qbf_pred_elim                         true
% 3.94/0.99  --qbf_split                             512
% 3.94/0.99  
% 3.94/0.99  ------ BMC1 Options
% 3.94/0.99  
% 3.94/0.99  --bmc1_incremental                      false
% 3.94/0.99  --bmc1_axioms                           reachable_all
% 3.94/0.99  --bmc1_min_bound                        0
% 3.94/0.99  --bmc1_max_bound                        -1
% 3.94/0.99  --bmc1_max_bound_default                -1
% 3.94/0.99  --bmc1_symbol_reachability              true
% 3.94/0.99  --bmc1_property_lemmas                  false
% 3.94/0.99  --bmc1_k_induction                      false
% 3.94/0.99  --bmc1_non_equiv_states                 false
% 3.94/0.99  --bmc1_deadlock                         false
% 3.94/0.99  --bmc1_ucm                              false
% 3.94/0.99  --bmc1_add_unsat_core                   none
% 3.94/0.99  --bmc1_unsat_core_children              false
% 3.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.94/0.99  --bmc1_out_stat                         full
% 3.94/0.99  --bmc1_ground_init                      false
% 3.94/0.99  --bmc1_pre_inst_next_state              false
% 3.94/0.99  --bmc1_pre_inst_state                   false
% 3.94/0.99  --bmc1_pre_inst_reach_state             false
% 3.94/0.99  --bmc1_out_unsat_core                   false
% 3.94/0.99  --bmc1_aig_witness_out                  false
% 3.94/0.99  --bmc1_verbose                          false
% 3.94/0.99  --bmc1_dump_clauses_tptp                false
% 3.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.94/0.99  --bmc1_dump_file                        -
% 3.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.94/0.99  --bmc1_ucm_extend_mode                  1
% 3.94/0.99  --bmc1_ucm_init_mode                    2
% 3.94/0.99  --bmc1_ucm_cone_mode                    none
% 3.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.94/0.99  --bmc1_ucm_relax_model                  4
% 3.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.94/0.99  --bmc1_ucm_layered_model                none
% 3.94/0.99  --bmc1_ucm_max_lemma_size               10
% 3.94/0.99  
% 3.94/0.99  ------ AIG Options
% 3.94/0.99  
% 3.94/0.99  --aig_mode                              false
% 3.94/0.99  
% 3.94/0.99  ------ Instantiation Options
% 3.94/0.99  
% 3.94/0.99  --instantiation_flag                    true
% 3.94/0.99  --inst_sos_flag                         true
% 3.94/0.99  --inst_sos_phase                        true
% 3.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.94/0.99  --inst_lit_sel_side                     num_symb
% 3.94/0.99  --inst_solver_per_active                1400
% 3.94/0.99  --inst_solver_calls_frac                1.
% 3.94/0.99  --inst_passive_queue_type               priority_queues
% 3.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.94/0.99  --inst_passive_queues_freq              [25;2]
% 3.94/0.99  --inst_dismatching                      true
% 3.94/0.99  --inst_eager_unprocessed_to_passive     true
% 3.94/0.99  --inst_prop_sim_given                   true
% 3.94/0.99  --inst_prop_sim_new                     false
% 3.94/0.99  --inst_subs_new                         false
% 3.94/0.99  --inst_eq_res_simp                      false
% 3.94/0.99  --inst_subs_given                       false
% 3.94/0.99  --inst_orphan_elimination               true
% 3.94/0.99  --inst_learning_loop_flag               true
% 3.94/0.99  --inst_learning_start                   3000
% 3.94/0.99  --inst_learning_factor                  2
% 3.94/0.99  --inst_start_prop_sim_after_learn       3
% 3.94/0.99  --inst_sel_renew                        solver
% 3.94/0.99  --inst_lit_activity_flag                true
% 3.94/0.99  --inst_restr_to_given                   false
% 3.94/0.99  --inst_activity_threshold               500
% 3.94/0.99  --inst_out_proof                        true
% 3.94/0.99  
% 3.94/0.99  ------ Resolution Options
% 3.94/0.99  
% 3.94/0.99  --resolution_flag                       true
% 3.94/0.99  --res_lit_sel                           adaptive
% 3.94/0.99  --res_lit_sel_side                      none
% 3.94/0.99  --res_ordering                          kbo
% 3.94/0.99  --res_to_prop_solver                    active
% 3.94/0.99  --res_prop_simpl_new                    false
% 3.94/0.99  --res_prop_simpl_given                  true
% 3.94/0.99  --res_passive_queue_type                priority_queues
% 3.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.94/0.99  --res_passive_queues_freq               [15;5]
% 3.94/0.99  --res_forward_subs                      full
% 3.94/0.99  --res_backward_subs                     full
% 3.94/0.99  --res_forward_subs_resolution           true
% 3.94/0.99  --res_backward_subs_resolution          true
% 3.94/0.99  --res_orphan_elimination                true
% 3.94/0.99  --res_time_limit                        2.
% 3.94/0.99  --res_out_proof                         true
% 3.94/0.99  
% 3.94/0.99  ------ Superposition Options
% 3.94/0.99  
% 3.94/0.99  --superposition_flag                    true
% 3.94/0.99  --sup_passive_queue_type                priority_queues
% 3.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.94/0.99  --demod_completeness_check              fast
% 3.94/0.99  --demod_use_ground                      true
% 3.94/0.99  --sup_to_prop_solver                    passive
% 3.94/0.99  --sup_prop_simpl_new                    true
% 3.94/0.99  --sup_prop_simpl_given                  true
% 3.94/0.99  --sup_fun_splitting                     true
% 3.94/0.99  --sup_smt_interval                      50000
% 3.94/0.99  
% 3.94/0.99  ------ Superposition Simplification Setup
% 3.94/0.99  
% 3.94/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.94/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.94/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.94/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.94/0.99  --sup_immed_triv                        [TrivRules]
% 3.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/0.99  --sup_immed_bw_main                     []
% 3.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/0.99  --sup_input_bw                          []
% 3.94/0.99  
% 3.94/0.99  ------ Combination Options
% 3.94/0.99  
% 3.94/0.99  --comb_res_mult                         3
% 3.94/0.99  --comb_sup_mult                         2
% 3.94/0.99  --comb_inst_mult                        10
% 3.94/0.99  
% 3.94/0.99  ------ Debug Options
% 3.94/0.99  
% 3.94/0.99  --dbg_backtrace                         false
% 3.94/0.99  --dbg_dump_prop_clauses                 false
% 3.94/0.99  --dbg_dump_prop_clauses_file            -
% 3.94/0.99  --dbg_out_stat                          false
% 3.94/0.99  ------ Parsing...
% 3.94/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.94/0.99  ------ Proving...
% 3.94/0.99  ------ Problem Properties 
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  clauses                                 31
% 3.94/0.99  conjectures                             13
% 3.94/0.99  EPR                                     10
% 3.94/0.99  Horn                                    25
% 3.94/0.99  unary                                   14
% 3.94/0.99  binary                                  5
% 3.94/0.99  lits                                    126
% 3.94/0.99  lits eq                                 17
% 3.94/0.99  fd_pure                                 0
% 3.94/0.99  fd_pseudo                               0
% 3.94/0.99  fd_cond                                 1
% 3.94/0.99  fd_pseudo_cond                          0
% 3.94/0.99  AC symbols                              0
% 3.94/0.99  
% 3.94/0.99  ------ Schedule dynamic 5 is on 
% 3.94/0.99  
% 3.94/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ 
% 3.94/0.99  Current options:
% 3.94/0.99  ------ 
% 3.94/0.99  
% 3.94/0.99  ------ Input Options
% 3.94/0.99  
% 3.94/0.99  --out_options                           all
% 3.94/0.99  --tptp_safe_out                         true
% 3.94/0.99  --problem_path                          ""
% 3.94/0.99  --include_path                          ""
% 3.94/0.99  --clausifier                            res/vclausify_rel
% 3.94/0.99  --clausifier_options                    ""
% 3.94/0.99  --stdin                                 false
% 3.94/0.99  --stats_out                             all
% 3.94/0.99  
% 3.94/0.99  ------ General Options
% 3.94/0.99  
% 3.94/0.99  --fof                                   false
% 3.94/0.99  --time_out_real                         305.
% 3.94/0.99  --time_out_virtual                      -1.
% 3.94/0.99  --symbol_type_check                     false
% 3.94/0.99  --clausify_out                          false
% 3.94/0.99  --sig_cnt_out                           false
% 3.94/0.99  --trig_cnt_out                          false
% 3.94/0.99  --trig_cnt_out_tolerance                1.
% 3.94/0.99  --trig_cnt_out_sk_spl                   false
% 3.94/0.99  --abstr_cl_out                          false
% 3.94/0.99  
% 3.94/0.99  ------ Global Options
% 3.94/0.99  
% 3.94/0.99  --schedule                              default
% 3.94/0.99  --add_important_lit                     false
% 3.94/0.99  --prop_solver_per_cl                    1000
% 3.94/0.99  --min_unsat_core                        false
% 3.94/0.99  --soft_assumptions                      false
% 3.94/0.99  --soft_lemma_size                       3
% 3.94/0.99  --prop_impl_unit_size                   0
% 3.94/0.99  --prop_impl_unit                        []
% 3.94/0.99  --share_sel_clauses                     true
% 3.94/0.99  --reset_solvers                         false
% 3.94/0.99  --bc_imp_inh                            [conj_cone]
% 3.94/0.99  --conj_cone_tolerance                   3.
% 3.94/0.99  --extra_neg_conj                        none
% 3.94/0.99  --large_theory_mode                     true
% 3.94/0.99  --prolific_symb_bound                   200
% 3.94/0.99  --lt_threshold                          2000
% 3.94/0.99  --clause_weak_htbl                      true
% 3.94/0.99  --gc_record_bc_elim                     false
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing Options
% 3.94/0.99  
% 3.94/0.99  --preprocessing_flag                    true
% 3.94/0.99  --time_out_prep_mult                    0.1
% 3.94/0.99  --splitting_mode                        input
% 3.94/0.99  --splitting_grd                         true
% 3.94/0.99  --splitting_cvd                         false
% 3.94/0.99  --splitting_cvd_svl                     false
% 3.94/0.99  --splitting_nvd                         32
% 3.94/0.99  --sub_typing                            true
% 3.94/0.99  --prep_gs_sim                           true
% 3.94/0.99  --prep_unflatten                        true
% 3.94/0.99  --prep_res_sim                          true
% 3.94/0.99  --prep_upred                            true
% 3.94/0.99  --prep_sem_filter                       exhaustive
% 3.94/0.99  --prep_sem_filter_out                   false
% 3.94/0.99  --pred_elim                             true
% 3.94/0.99  --res_sim_input                         true
% 3.94/0.99  --eq_ax_congr_red                       true
% 3.94/0.99  --pure_diseq_elim                       true
% 3.94/0.99  --brand_transform                       false
% 3.94/0.99  --non_eq_to_eq                          false
% 3.94/0.99  --prep_def_merge                        true
% 3.94/0.99  --prep_def_merge_prop_impl              false
% 3.94/0.99  --prep_def_merge_mbd                    true
% 3.94/0.99  --prep_def_merge_tr_red                 false
% 3.94/0.99  --prep_def_merge_tr_cl                  false
% 3.94/0.99  --smt_preprocessing                     true
% 3.94/0.99  --smt_ac_axioms                         fast
% 3.94/0.99  --preprocessed_out                      false
% 3.94/0.99  --preprocessed_stats                    false
% 3.94/0.99  
% 3.94/0.99  ------ Abstraction refinement Options
% 3.94/0.99  
% 3.94/0.99  --abstr_ref                             []
% 3.94/0.99  --abstr_ref_prep                        false
% 3.94/0.99  --abstr_ref_until_sat                   false
% 3.94/0.99  --abstr_ref_sig_restrict                funpre
% 3.94/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.94/0.99  --abstr_ref_under                       []
% 3.94/0.99  
% 3.94/0.99  ------ SAT Options
% 3.94/0.99  
% 3.94/0.99  --sat_mode                              false
% 3.94/0.99  --sat_fm_restart_options                ""
% 3.94/0.99  --sat_gr_def                            false
% 3.94/0.99  --sat_epr_types                         true
% 3.94/0.99  --sat_non_cyclic_types                  false
% 3.94/0.99  --sat_finite_models                     false
% 3.94/0.99  --sat_fm_lemmas                         false
% 3.94/0.99  --sat_fm_prep                           false
% 3.94/0.99  --sat_fm_uc_incr                        true
% 3.94/0.99  --sat_out_model                         small
% 3.94/0.99  --sat_out_clauses                       false
% 3.94/0.99  
% 3.94/0.99  ------ QBF Options
% 3.94/0.99  
% 3.94/0.99  --qbf_mode                              false
% 3.94/0.99  --qbf_elim_univ                         false
% 3.94/0.99  --qbf_dom_inst                          none
% 3.94/0.99  --qbf_dom_pre_inst                      false
% 3.94/0.99  --qbf_sk_in                             false
% 3.94/0.99  --qbf_pred_elim                         true
% 3.94/0.99  --qbf_split                             512
% 3.94/0.99  
% 3.94/0.99  ------ BMC1 Options
% 3.94/0.99  
% 3.94/0.99  --bmc1_incremental                      false
% 3.94/0.99  --bmc1_axioms                           reachable_all
% 3.94/0.99  --bmc1_min_bound                        0
% 3.94/0.99  --bmc1_max_bound                        -1
% 3.94/0.99  --bmc1_max_bound_default                -1
% 3.94/0.99  --bmc1_symbol_reachability              true
% 3.94/0.99  --bmc1_property_lemmas                  false
% 3.94/0.99  --bmc1_k_induction                      false
% 3.94/0.99  --bmc1_non_equiv_states                 false
% 3.94/0.99  --bmc1_deadlock                         false
% 3.94/0.99  --bmc1_ucm                              false
% 3.94/0.99  --bmc1_add_unsat_core                   none
% 3.94/0.99  --bmc1_unsat_core_children              false
% 3.94/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.94/0.99  --bmc1_out_stat                         full
% 3.94/0.99  --bmc1_ground_init                      false
% 3.94/0.99  --bmc1_pre_inst_next_state              false
% 3.94/0.99  --bmc1_pre_inst_state                   false
% 3.94/0.99  --bmc1_pre_inst_reach_state             false
% 3.94/0.99  --bmc1_out_unsat_core                   false
% 3.94/0.99  --bmc1_aig_witness_out                  false
% 3.94/0.99  --bmc1_verbose                          false
% 3.94/0.99  --bmc1_dump_clauses_tptp                false
% 3.94/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.94/0.99  --bmc1_dump_file                        -
% 3.94/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.94/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.94/0.99  --bmc1_ucm_extend_mode                  1
% 3.94/0.99  --bmc1_ucm_init_mode                    2
% 3.94/0.99  --bmc1_ucm_cone_mode                    none
% 3.94/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.94/0.99  --bmc1_ucm_relax_model                  4
% 3.94/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.94/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.94/0.99  --bmc1_ucm_layered_model                none
% 3.94/0.99  --bmc1_ucm_max_lemma_size               10
% 3.94/0.99  
% 3.94/0.99  ------ AIG Options
% 3.94/0.99  
% 3.94/0.99  --aig_mode                              false
% 3.94/0.99  
% 3.94/0.99  ------ Instantiation Options
% 3.94/0.99  
% 3.94/0.99  --instantiation_flag                    true
% 3.94/0.99  --inst_sos_flag                         true
% 3.94/0.99  --inst_sos_phase                        true
% 3.94/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.94/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.94/0.99  --inst_lit_sel_side                     none
% 3.94/0.99  --inst_solver_per_active                1400
% 3.94/0.99  --inst_solver_calls_frac                1.
% 3.94/0.99  --inst_passive_queue_type               priority_queues
% 3.94/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.94/0.99  --inst_passive_queues_freq              [25;2]
% 3.94/0.99  --inst_dismatching                      true
% 3.94/0.99  --inst_eager_unprocessed_to_passive     true
% 3.94/0.99  --inst_prop_sim_given                   true
% 3.94/0.99  --inst_prop_sim_new                     false
% 3.94/0.99  --inst_subs_new                         false
% 3.94/0.99  --inst_eq_res_simp                      false
% 3.94/0.99  --inst_subs_given                       false
% 3.94/0.99  --inst_orphan_elimination               true
% 3.94/0.99  --inst_learning_loop_flag               true
% 3.94/0.99  --inst_learning_start                   3000
% 3.94/0.99  --inst_learning_factor                  2
% 3.94/0.99  --inst_start_prop_sim_after_learn       3
% 3.94/0.99  --inst_sel_renew                        solver
% 3.94/0.99  --inst_lit_activity_flag                true
% 3.94/0.99  --inst_restr_to_given                   false
% 3.94/0.99  --inst_activity_threshold               500
% 3.94/0.99  --inst_out_proof                        true
% 3.94/0.99  
% 3.94/0.99  ------ Resolution Options
% 3.94/0.99  
% 3.94/0.99  --resolution_flag                       false
% 3.94/0.99  --res_lit_sel                           adaptive
% 3.94/0.99  --res_lit_sel_side                      none
% 3.94/0.99  --res_ordering                          kbo
% 3.94/0.99  --res_to_prop_solver                    active
% 3.94/0.99  --res_prop_simpl_new                    false
% 3.94/0.99  --res_prop_simpl_given                  true
% 3.94/0.99  --res_passive_queue_type                priority_queues
% 3.94/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.94/0.99  --res_passive_queues_freq               [15;5]
% 3.94/0.99  --res_forward_subs                      full
% 3.94/0.99  --res_backward_subs                     full
% 3.94/0.99  --res_forward_subs_resolution           true
% 3.94/0.99  --res_backward_subs_resolution          true
% 3.94/0.99  --res_orphan_elimination                true
% 3.94/0.99  --res_time_limit                        2.
% 3.94/0.99  --res_out_proof                         true
% 3.94/0.99  
% 3.94/0.99  ------ Superposition Options
% 3.94/0.99  
% 3.94/0.99  --superposition_flag                    true
% 3.94/0.99  --sup_passive_queue_type                priority_queues
% 3.94/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.94/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.94/0.99  --demod_completeness_check              fast
% 3.94/0.99  --demod_use_ground                      true
% 3.94/0.99  --sup_to_prop_solver                    passive
% 3.94/0.99  --sup_prop_simpl_new                    true
% 3.94/0.99  --sup_prop_simpl_given                  true
% 3.94/0.99  --sup_fun_splitting                     true
% 3.94/0.99  --sup_smt_interval                      50000
% 3.94/0.99  
% 3.94/0.99  ------ Superposition Simplification Setup
% 3.94/0.99  
% 3.94/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.94/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.94/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.94/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.94/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.94/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.94/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.94/0.99  --sup_immed_triv                        [TrivRules]
% 3.94/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/0.99  --sup_immed_bw_main                     []
% 3.94/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.94/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.94/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.94/0.99  --sup_input_bw                          []
% 3.94/0.99  
% 3.94/0.99  ------ Combination Options
% 3.94/0.99  
% 3.94/0.99  --comb_res_mult                         3
% 3.94/0.99  --comb_sup_mult                         2
% 3.94/0.99  --comb_inst_mult                        10
% 3.94/0.99  
% 3.94/0.99  ------ Debug Options
% 3.94/0.99  
% 3.94/0.99  --dbg_backtrace                         false
% 3.94/0.99  --dbg_dump_prop_clauses                 false
% 3.94/0.99  --dbg_dump_prop_clauses_file            -
% 3.94/0.99  --dbg_out_stat                          false
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  ------ Proving...
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  % SZS status Theorem for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  fof(f15,conjecture,(
% 3.94/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f16,negated_conjecture,(
% 3.94/0.99    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.94/0.99    inference(negated_conjecture,[],[f15])).
% 3.94/0.99  
% 3.94/0.99  fof(f37,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f16])).
% 3.94/0.99  
% 3.94/0.99  fof(f38,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.94/0.99    inference(flattening,[],[f37])).
% 3.94/0.99  
% 3.94/0.99  fof(f48,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f47,plain,(
% 3.94/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f46,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f45,plain,(
% 3.94/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f44,plain,(
% 3.94/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f43,plain,(
% 3.94/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.94/0.99    introduced(choice_axiom,[])).
% 3.94/0.99  
% 3.94/0.99  fof(f49,plain,(
% 3.94/0.99    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f38,f48,f47,f46,f45,f44,f43])).
% 3.94/0.99  
% 3.94/0.99  fof(f76,plain,(
% 3.94/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f4,axiom,(
% 3.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f19,plain,(
% 3.94/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.94/0.99    inference(ennf_transformation,[],[f4])).
% 3.94/0.99  
% 3.94/0.99  fof(f54,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f19])).
% 3.94/0.99  
% 3.94/0.99  fof(f80,plain,(
% 3.94/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f12,axiom,(
% 3.94/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f31,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.94/0.99    inference(ennf_transformation,[],[f12])).
% 3.94/0.99  
% 3.94/0.99  fof(f32,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.94/0.99    inference(flattening,[],[f31])).
% 3.94/0.99  
% 3.94/0.99  fof(f64,plain,(
% 3.94/0.99    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f32])).
% 3.94/0.99  
% 3.94/0.99  fof(f78,plain,(
% 3.94/0.99    v1_funct_1(sK4)),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f83,plain,(
% 3.94/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f81,plain,(
% 3.94/0.99    v1_funct_1(sK5)),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f13,axiom,(
% 3.94/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f33,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f13])).
% 3.94/0.99  
% 3.94/0.99  fof(f34,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.94/0.99    inference(flattening,[],[f33])).
% 3.94/0.99  
% 3.94/0.99  fof(f41,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.94/0.99    inference(nnf_transformation,[],[f34])).
% 3.94/0.99  
% 3.94/0.99  fof(f42,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.94/0.99    inference(flattening,[],[f41])).
% 3.94/0.99  
% 3.94/0.99  fof(f65,plain,(
% 3.94/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f42])).
% 3.94/0.99  
% 3.94/0.99  fof(f88,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.94/0.99    inference(equality_resolution,[],[f65])).
% 3.94/0.99  
% 3.94/0.99  fof(f14,axiom,(
% 3.94/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f35,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.94/0.99    inference(ennf_transformation,[],[f14])).
% 3.94/0.99  
% 3.94/0.99  fof(f36,plain,(
% 3.94/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.94/0.99    inference(flattening,[],[f35])).
% 3.94/0.99  
% 3.94/0.99  fof(f68,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f36])).
% 3.94/0.99  
% 3.94/0.99  fof(f69,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f36])).
% 3.94/0.99  
% 3.94/0.99  fof(f70,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f36])).
% 3.94/0.99  
% 3.94/0.99  fof(f72,plain,(
% 3.94/0.99    ~v1_xboole_0(sK1)),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f75,plain,(
% 3.94/0.99    ~v1_xboole_0(sK3)),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f82,plain,(
% 3.94/0.99    v1_funct_2(sK5,sK3,sK1)),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f73,plain,(
% 3.94/0.99    ~v1_xboole_0(sK2)),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f79,plain,(
% 3.94/0.99    v1_funct_2(sK4,sK2,sK1)),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f5,axiom,(
% 3.94/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f20,plain,(
% 3.94/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f5])).
% 3.94/0.99  
% 3.94/0.99  fof(f55,plain,(
% 3.94/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f20])).
% 3.94/0.99  
% 3.94/0.99  fof(f1,axiom,(
% 3.94/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f39,plain,(
% 3.94/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.94/0.99    inference(nnf_transformation,[],[f1])).
% 3.94/0.99  
% 3.94/0.99  fof(f50,plain,(
% 3.94/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f39])).
% 3.94/0.99  
% 3.94/0.99  fof(f9,axiom,(
% 3.94/0.99    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f27,plain,(
% 3.94/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.94/0.99    inference(ennf_transformation,[],[f9])).
% 3.94/0.99  
% 3.94/0.99  fof(f28,plain,(
% 3.94/0.99    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.94/0.99    inference(flattening,[],[f27])).
% 3.94/0.99  
% 3.94/0.99  fof(f40,plain,(
% 3.94/0.99    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.94/0.99    inference(nnf_transformation,[],[f28])).
% 3.94/0.99  
% 3.94/0.99  fof(f60,plain,(
% 3.94/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f40])).
% 3.94/0.99  
% 3.94/0.99  fof(f77,plain,(
% 3.94/0.99    r1_subset_1(sK2,sK3)),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f10,axiom,(
% 3.94/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f29,plain,(
% 3.94/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.94/0.99    inference(ennf_transformation,[],[f10])).
% 3.94/0.99  
% 3.94/0.99  fof(f62,plain,(
% 3.94/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.94/0.99    inference(cnf_transformation,[],[f29])).
% 3.94/0.99  
% 3.94/0.99  fof(f2,axiom,(
% 3.94/0.99    v1_xboole_0(k1_xboole_0)),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f52,plain,(
% 3.94/0.99    v1_xboole_0(k1_xboole_0)),
% 3.94/0.99    inference(cnf_transformation,[],[f2])).
% 3.94/0.99  
% 3.94/0.99  fof(f6,axiom,(
% 3.94/0.99    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f21,plain,(
% 3.94/0.99    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 3.94/0.99    inference(ennf_transformation,[],[f6])).
% 3.94/0.99  
% 3.94/0.99  fof(f22,plain,(
% 3.94/0.99    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 3.94/0.99    inference(flattening,[],[f21])).
% 3.94/0.99  
% 3.94/0.99  fof(f56,plain,(
% 3.94/0.99    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f22])).
% 3.94/0.99  
% 3.94/0.99  fof(f3,axiom,(
% 3.94/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.94/0.99  
% 3.94/0.99  fof(f18,plain,(
% 3.94/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.94/0.99    inference(ennf_transformation,[],[f3])).
% 3.94/0.99  
% 3.94/0.99  fof(f53,plain,(
% 3.94/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f18])).
% 3.94/0.99  
% 3.94/0.99  fof(f66,plain,(
% 3.94/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.94/0.99    inference(cnf_transformation,[],[f42])).
% 3.94/0.99  
% 3.94/0.99  fof(f87,plain,(
% 3.94/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.94/0.99    inference(equality_resolution,[],[f66])).
% 3.94/0.99  
% 3.94/0.99  fof(f71,plain,(
% 3.94/0.99    ~v1_xboole_0(sK0)),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f84,plain,(
% 3.94/0.99    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  fof(f74,plain,(
% 3.94/0.99    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.94/0.99    inference(cnf_transformation,[],[f49])).
% 3.94/0.99  
% 3.94/0.99  cnf(c_29,negated_conjecture,
% 3.94/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1215,plain,
% 3.94/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.94/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1231,plain,
% 3.94/0.99      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2394,plain,
% 3.94/0.99      ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1215,c_1231]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_25,negated_conjecture,
% 3.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 3.94/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1218,plain,
% 3.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_14,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.94/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1226,plain,
% 3.94/0.99      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3076,plain,
% 3.94/0.99      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
% 3.94/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1218,c_1226]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_27,negated_conjecture,
% 3.94/0.99      ( v1_funct_1(sK4) ),
% 3.94/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_42,plain,
% 3.94/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3210,plain,
% 3.94/0.99      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_3076,c_42]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_22,negated_conjecture,
% 3.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 3.94/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1221,plain,
% 3.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3075,plain,
% 3.94/0.99      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
% 3.94/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1221,c_1226]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_24,negated_conjecture,
% 3.94/0.99      ( v1_funct_1(sK5) ),
% 3.94/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_45,plain,
% 3.94/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3198,plain,
% 3.94/0.99      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_3075,c_45]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_17,plain,
% 3.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.94/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.94/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.94/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.94/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(X3)
% 3.94/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.94/0.99      | v1_xboole_0(X5)
% 3.94/0.99      | v1_xboole_0(X2)
% 3.94/0.99      | v1_xboole_0(X4)
% 3.94/0.99      | v1_xboole_0(X1)
% 3.94/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.94/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_20,plain,
% 3.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.94/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.94/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(X3)
% 3.94/0.99      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.94/0.99      | v1_xboole_0(X5)
% 3.94/0.99      | v1_xboole_0(X2)
% 3.94/0.99      | v1_xboole_0(X4)
% 3.94/0.99      | v1_xboole_0(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_19,plain,
% 3.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.94/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.94/0.99      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.94/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(X3)
% 3.94/0.99      | v1_xboole_0(X5)
% 3.94/0.99      | v1_xboole_0(X2)
% 3.94/0.99      | v1_xboole_0(X4)
% 3.94/0.99      | v1_xboole_0(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_18,plain,
% 3.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.94/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.94/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.94/0.99      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(X3)
% 3.94/0.99      | v1_xboole_0(X5)
% 3.94/0.99      | v1_xboole_0(X2)
% 3.94/0.99      | v1_xboole_0(X4)
% 3.94/0.99      | v1_xboole_0(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_184,plain,
% 3.94/0.99      ( ~ v1_funct_1(X3)
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.94/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.94/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.94/0.99      | v1_xboole_0(X5)
% 3.94/0.99      | v1_xboole_0(X2)
% 3.94/0.99      | v1_xboole_0(X4)
% 3.94/0.99      | v1_xboole_0(X1)
% 3.94/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_17,c_20,c_19,c_18]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_185,plain,
% 3.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.94/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.94/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(X3)
% 3.94/0.99      | v1_xboole_0(X1)
% 3.94/0.99      | v1_xboole_0(X2)
% 3.94/0.99      | v1_xboole_0(X4)
% 3.94/0.99      | v1_xboole_0(X5)
% 3.94/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_184]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1209,plain,
% 3.94/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 3.94/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.94/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.94/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.94/0.99      | v1_funct_1(X2) != iProver_top
% 3.94/0.99      | v1_funct_1(X5) != iProver_top
% 3.94/0.99      | v1_xboole_0(X3) = iProver_top
% 3.94/0.99      | v1_xboole_0(X1) = iProver_top
% 3.94/0.99      | v1_xboole_0(X4) = iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_185]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3790,plain,
% 3.94/0.99      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 3.94/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.94/0.99      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.94/0.99      | v1_funct_1(X1) != iProver_top
% 3.94/0.99      | v1_funct_1(sK5) != iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top
% 3.94/0.99      | v1_xboole_0(X2) = iProver_top
% 3.94/0.99      | v1_xboole_0(sK1) = iProver_top
% 3.94/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3198,c_1209]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_33,negated_conjecture,
% 3.94/0.99      ( ~ v1_xboole_0(sK1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_36,plain,
% 3.94/0.99      ( v1_xboole_0(sK1) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_30,negated_conjecture,
% 3.94/0.99      ( ~ v1_xboole_0(sK3) ),
% 3.94/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_39,plain,
% 3.94/0.99      ( v1_xboole_0(sK3) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_23,negated_conjecture,
% 3.94/0.99      ( v1_funct_2(sK5,sK3,sK1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_46,plain,
% 3.94/0.99      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_47,plain,
% 3.94/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6542,plain,
% 3.94/0.99      ( v1_funct_1(X1) != iProver_top
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.94/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.94/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 3.94/0.99      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top
% 3.94/0.99      | v1_xboole_0(X2) = iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_3790,c_36,c_39,c_45,c_46,c_47]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6543,plain,
% 3.94/0.99      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
% 3.94/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X2)) != iProver_top
% 3.94/0.99      | v1_funct_1(X1) != iProver_top
% 3.94/0.99      | v1_xboole_0(X2) = iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_6542]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6549,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.94/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 3.94/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.94/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.94/0.99      | v1_funct_1(sK4) != iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top
% 3.94/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3210,c_6543]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_32,negated_conjecture,
% 3.94/0.99      ( ~ v1_xboole_0(sK2) ),
% 3.94/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_37,plain,
% 3.94/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_26,negated_conjecture,
% 3.94/0.99      ( v1_funct_2(sK4,sK2,sK1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_43,plain,
% 3.94/0.99      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_44,plain,
% 3.94/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_5,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.94/0.99      | ~ v1_xboole_0(X1)
% 3.94/0.99      | v1_xboole_0(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1315,plain,
% 3.94/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.94/0.99      | ~ v1_xboole_0(X0)
% 3.94/0.99      | v1_xboole_0(sK2) ),
% 3.94/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1316,plain,
% 3.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.94/0.99      | v1_xboole_0(X0) != iProver_top
% 3.94/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_1315]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6584,plain,
% 3.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.94/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_6549,c_37,c_42,c_43,c_44,c_1316]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6585,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.94/0.99      | k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3))
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_6584]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6590,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.94/0.99      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_2394,c_6585]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1,plain,
% 3.94/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.94/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_253,plain,
% 3.94/0.99      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.94/0.99      inference(prop_impl,[status(thm)],[c_1]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_11,plain,
% 3.94/0.99      ( ~ r1_subset_1(X0,X1)
% 3.94/0.99      | r1_xboole_0(X0,X1)
% 3.94/0.99      | v1_xboole_0(X0)
% 3.94/0.99      | v1_xboole_0(X1) ),
% 3.94/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_28,negated_conjecture,
% 3.94/0.99      ( r1_subset_1(sK2,sK3) ),
% 3.94/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_466,plain,
% 3.94/0.99      ( r1_xboole_0(X0,X1)
% 3.94/0.99      | v1_xboole_0(X0)
% 3.94/0.99      | v1_xboole_0(X1)
% 3.94/0.99      | sK3 != X1
% 3.94/0.99      | sK2 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_467,plain,
% 3.94/0.99      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_466]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_469,plain,
% 3.94/0.99      ( r1_xboole_0(sK2,sK3) ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_467,c_32,c_30]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_506,plain,
% 3.94/0.99      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 3.94/0.99      inference(resolution_lifted,[status(thm)],[c_253,c_469]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_507,plain,
% 3.94/0.99      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 3.94/0.99      inference(unflattening,[status(thm)],[c_506]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_12,plain,
% 3.94/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | v1_relat_1(X0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1227,plain,
% 3.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.94/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2216,plain,
% 3.94/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1221,c_1227]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2,plain,
% 3.94/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1233,plain,
% 3.94/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_7,plain,
% 3.94/0.99      ( ~ v1_relat_1(X0)
% 3.94/0.99      | ~ v1_xboole_0(X1)
% 3.94/0.99      | v1_xboole_0(k7_relat_1(X0,X1)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1228,plain,
% 3.94/0.99      ( v1_relat_1(X0) != iProver_top
% 3.94/0.99      | v1_xboole_0(X1) != iProver_top
% 3.94/0.99      | v1_xboole_0(k7_relat_1(X0,X1)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3,plain,
% 3.94/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.94/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1232,plain,
% 3.94/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2439,plain,
% 3.94/0.99      ( k7_relat_1(X0,X1) = k1_xboole_0
% 3.94/0.99      | v1_relat_1(X0) != iProver_top
% 3.94/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1228,c_1232]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3920,plain,
% 3.94/0.99      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.94/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1233,c_2439]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3928,plain,
% 3.94/0.99      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_2216,c_3920]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6591,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.94/0.99      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 3.94/0.99      inference(light_normalisation,[status(thm)],[c_6590,c_507,c_3928]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6592,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.94/0.99      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_6591,c_2394]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2217,plain,
% 3.94/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_1218,c_1227]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3929,plain,
% 3.94/0.99      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_2217,c_3920]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6593,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.94/0.99      | k1_xboole_0 != k1_xboole_0
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 3.94/0.99      inference(light_normalisation,[status(thm)],[c_6592,c_507,c_3929]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_6594,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 3.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_6593]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_16,plain,
% 3.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.94/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.94/0.99      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.94/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.94/0.99      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(X3)
% 3.94/0.99      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.94/0.99      | v1_xboole_0(X5)
% 3.94/0.99      | v1_xboole_0(X2)
% 3.94/0.99      | v1_xboole_0(X4)
% 3.94/0.99      | v1_xboole_0(X1)
% 3.94/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.94/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_191,plain,
% 3.94/0.99      ( ~ v1_funct_1(X3)
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.94/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.94/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.94/0.99      | v1_xboole_0(X5)
% 3.94/0.99      | v1_xboole_0(X2)
% 3.94/0.99      | v1_xboole_0(X4)
% 3.94/0.99      | v1_xboole_0(X1)
% 3.94/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_16,c_20,c_19,c_18]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_192,plain,
% 3.94/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.94/0.99      | ~ v1_funct_2(X3,X4,X2)
% 3.94/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.94/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.94/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.94/0.99      | ~ v1_funct_1(X0)
% 3.94/0.99      | ~ v1_funct_1(X3)
% 3.94/0.99      | v1_xboole_0(X1)
% 3.94/0.99      | v1_xboole_0(X2)
% 3.94/0.99      | v1_xboole_0(X4)
% 3.94/0.99      | v1_xboole_0(X5)
% 3.94/0.99      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_191]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_1208,plain,
% 3.94/0.99      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.94/0.99      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 3.94/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.94/0.99      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.94/0.99      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.94/0.99      | v1_funct_1(X2) != iProver_top
% 3.94/0.99      | v1_funct_1(X5) != iProver_top
% 3.94/0.99      | v1_xboole_0(X3) = iProver_top
% 3.94/0.99      | v1_xboole_0(X1) = iProver_top
% 3.94/0.99      | v1_xboole_0(X4) = iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3023,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),sK3) = X3
% 3.94/0.99      | k2_partfun1(sK3,X1,X3,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK3))
% 3.94/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.94/0.99      | v1_funct_2(X3,sK3,X1) != iProver_top
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | v1_funct_1(X3) != iProver_top
% 3.94/0.99      | v1_funct_1(X2) != iProver_top
% 3.94/0.99      | v1_xboole_0(X1) = iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top
% 3.94/0.99      | v1_xboole_0(sK3) = iProver_top
% 3.94/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_2394,c_1208]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3027,plain,
% 3.94/0.99      ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK3)) != k2_partfun1(sK3,X1,X3,k3_xboole_0(X0,sK3))
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),sK3) = X3
% 3.94/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.94/0.99      | v1_funct_2(X3,sK3,X1) != iProver_top
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | v1_funct_1(X3) != iProver_top
% 3.94/0.99      | v1_funct_1(X2) != iProver_top
% 3.94/0.99      | v1_xboole_0(X1) = iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top
% 3.94/0.99      | v1_xboole_0(sK3) = iProver_top
% 3.94/0.99      | v1_xboole_0(sK0) = iProver_top ),
% 3.94/0.99      inference(light_normalisation,[status(thm)],[c_3023,c_2394]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_34,negated_conjecture,
% 3.94/0.99      ( ~ v1_xboole_0(sK0) ),
% 3.94/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_35,plain,
% 3.94/0.99      ( v1_xboole_0(sK0) != iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_40,plain,
% 3.94/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4225,plain,
% 3.94/0.99      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | v1_funct_2(X3,sK3,X1) != iProver_top
% 3.94/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),sK3) = X3
% 3.94/0.99      | k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK3)) != k2_partfun1(sK3,X1,X3,k3_xboole_0(X0,sK3))
% 3.94/0.99      | v1_funct_1(X3) != iProver_top
% 3.94/0.99      | v1_funct_1(X2) != iProver_top
% 3.94/0.99      | v1_xboole_0(X1) = iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_3027,c_35,c_39,c_40]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4226,plain,
% 3.94/0.99      ( k2_partfun1(X0,X1,X2,k3_xboole_0(X0,sK3)) != k2_partfun1(sK3,X1,X3,k3_xboole_0(X0,sK3))
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),sK3) = X3
% 3.94/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.94/0.99      | v1_funct_2(X3,sK3,X1) != iProver_top
% 3.94/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | v1_funct_1(X3) != iProver_top
% 3.94/0.99      | v1_funct_1(X2) != iProver_top
% 3.94/0.99      | v1_xboole_0(X1) = iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_4225]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4233,plain,
% 3.94/0.99      ( k2_partfun1(X0,sK1,X1,k3_xboole_0(X0,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0,sK3))
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 3.94/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.94/0.99      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 3.94/0.99      | v1_funct_1(X1) != iProver_top
% 3.94/0.99      | v1_funct_1(sK5) != iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top
% 3.94/0.99      | v1_xboole_0(sK1) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3198,c_4226]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4600,plain,
% 3.94/0.99      ( v1_xboole_0(X0) = iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.94/0.99      | k2_partfun1(X0,sK1,X1,k3_xboole_0(X0,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0,sK3))
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 3.94/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.94/0.99      | v1_funct_1(X1) != iProver_top ),
% 3.94/0.99      inference(global_propositional_subsumption,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_4233,c_36,c_45,c_46,c_47]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4601,plain,
% 3.94/0.99      ( k2_partfun1(X0,sK1,X1,k3_xboole_0(X0,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0,sK3))
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) = sK5
% 3.94/0.99      | v1_funct_2(X1,X0,sK1) != iProver_top
% 3.94/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | v1_funct_1(X1) != iProver_top
% 3.94/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.94/0.99      inference(renaming,[status(thm)],[c_4600]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4607,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.94/0.99      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 3.94/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.94/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | v1_funct_1(sK4) != iProver_top
% 3.94/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.94/0.99      inference(superposition,[status(thm)],[c_3210,c_4601]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4610,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.94/0.99      | k1_xboole_0 != k1_xboole_0
% 3.94/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.94/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | v1_funct_1(sK4) != iProver_top
% 3.94/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.94/0.99      inference(light_normalisation,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_4607,c_507,c_3928,c_3929]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_4611,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 3.94/0.99      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 3.94/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.94/0.99      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 3.94/0.99      | v1_funct_1(sK4) != iProver_top
% 3.94/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_4610]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_21,negated_conjecture,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.94/0.99      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2869,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.94/0.99      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_2394,c_21]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_2870,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.94/0.99      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 3.94/0.99      inference(light_normalisation,[status(thm)],[c_2869,c_507]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3241,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.94/0.99      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_2870,c_3198,c_3210]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3968,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.94/0.99      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 3.94/0.99      inference(demodulation,[status(thm)],[c_3928,c_3241]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3969,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 3.94/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.94/0.99      inference(light_normalisation,[status(thm)],[c_3968,c_3929]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_3970,plain,
% 3.94/0.99      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 3.94/0.99      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 3.94/0.99      inference(equality_resolution_simp,[status(thm)],[c_3969]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_31,negated_conjecture,
% 3.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 3.94/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(c_38,plain,
% 3.94/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 3.94/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.94/0.99  
% 3.94/0.99  cnf(contradiction,plain,
% 3.94/0.99      ( $false ),
% 3.94/0.99      inference(minisat,
% 3.94/0.99                [status(thm)],
% 3.94/0.99                [c_6594,c_4611,c_3970,c_44,c_43,c_42,c_40,c_38,c_37]) ).
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.94/0.99  
% 3.94/0.99  ------                               Statistics
% 3.94/0.99  
% 3.94/0.99  ------ General
% 3.94/0.99  
% 3.94/0.99  abstr_ref_over_cycles:                  0
% 3.94/0.99  abstr_ref_under_cycles:                 0
% 3.94/0.99  gc_basic_clause_elim:                   0
% 3.94/0.99  forced_gc_time:                         0
% 3.94/0.99  parsing_time:                           0.011
% 3.94/0.99  unif_index_cands_time:                  0.
% 3.94/0.99  unif_index_add_time:                    0.
% 3.94/0.99  orderings_time:                         0.
% 3.94/0.99  out_proof_time:                         0.013
% 3.94/0.99  total_time:                             0.451
% 3.94/0.99  num_of_symbols:                         54
% 3.94/0.99  num_of_terms:                           21150
% 3.94/0.99  
% 3.94/0.99  ------ Preprocessing
% 3.94/0.99  
% 3.94/0.99  num_of_splits:                          0
% 3.94/0.99  num_of_split_atoms:                     0
% 3.94/0.99  num_of_reused_defs:                     0
% 3.94/0.99  num_eq_ax_congr_red:                    7
% 3.94/0.99  num_of_sem_filtered_clauses:            1
% 3.94/0.99  num_of_subtypes:                        0
% 3.94/0.99  monotx_restored_types:                  0
% 3.94/0.99  sat_num_of_epr_types:                   0
% 3.94/0.99  sat_num_of_non_cyclic_types:            0
% 3.94/0.99  sat_guarded_non_collapsed_types:        0
% 3.94/0.99  num_pure_diseq_elim:                    0
% 3.94/0.99  simp_replaced_by:                       0
% 3.94/0.99  res_preprocessed:                       159
% 3.94/0.99  prep_upred:                             0
% 3.94/0.99  prep_unflattend:                        6
% 3.94/0.99  smt_new_axioms:                         0
% 3.94/0.99  pred_elim_cands:                        5
% 3.94/0.99  pred_elim:                              3
% 3.94/0.99  pred_elim_cl:                           4
% 3.94/0.99  pred_elim_cycles:                       5
% 3.94/0.99  merged_defs:                            2
% 3.94/0.99  merged_defs_ncl:                        0
% 3.94/0.99  bin_hyper_res:                          2
% 3.94/0.99  prep_cycles:                            4
% 3.94/0.99  pred_elim_time:                         0.003
% 3.94/0.99  splitting_time:                         0.
% 3.94/0.99  sem_filter_time:                        0.
% 3.94/0.99  monotx_time:                            0.001
% 3.94/0.99  subtype_inf_time:                       0.
% 3.94/0.99  
% 3.94/0.99  ------ Problem properties
% 3.94/0.99  
% 3.94/0.99  clauses:                                31
% 3.94/0.99  conjectures:                            13
% 3.94/0.99  epr:                                    10
% 3.94/0.99  horn:                                   25
% 3.94/0.99  ground:                                 15
% 3.94/0.99  unary:                                  14
% 3.94/0.99  binary:                                 5
% 3.94/0.99  lits:                                   126
% 3.94/0.99  lits_eq:                                17
% 3.94/0.99  fd_pure:                                0
% 3.94/0.99  fd_pseudo:                              0
% 3.94/0.99  fd_cond:                                1
% 3.94/0.99  fd_pseudo_cond:                         0
% 3.94/0.99  ac_symbols:                             0
% 3.94/0.99  
% 3.94/0.99  ------ Propositional Solver
% 3.94/0.99  
% 3.94/0.99  prop_solver_calls:                      28
% 3.94/0.99  prop_fast_solver_calls:                 1961
% 3.94/0.99  smt_solver_calls:                       0
% 3.94/0.99  smt_fast_solver_calls:                  0
% 3.94/0.99  prop_num_of_clauses:                    3722
% 3.94/0.99  prop_preprocess_simplified:             8769
% 3.94/0.99  prop_fo_subsumed:                       124
% 3.94/0.99  prop_solver_time:                       0.
% 3.94/0.99  smt_solver_time:                        0.
% 3.94/0.99  smt_fast_solver_time:                   0.
% 3.94/0.99  prop_fast_solver_time:                  0.
% 3.94/0.99  prop_unsat_core_time:                   0.
% 3.94/0.99  
% 3.94/0.99  ------ QBF
% 3.94/0.99  
% 3.94/0.99  qbf_q_res:                              0
% 3.94/0.99  qbf_num_tautologies:                    0
% 3.94/0.99  qbf_prep_cycles:                        0
% 3.94/0.99  
% 3.94/0.99  ------ BMC1
% 3.94/0.99  
% 3.94/0.99  bmc1_current_bound:                     -1
% 3.94/0.99  bmc1_last_solved_bound:                 -1
% 3.94/0.99  bmc1_unsat_core_size:                   -1
% 3.94/0.99  bmc1_unsat_core_parents_size:           -1
% 3.94/0.99  bmc1_merge_next_fun:                    0
% 3.94/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.94/0.99  
% 3.94/0.99  ------ Instantiation
% 3.94/0.99  
% 3.94/0.99  inst_num_of_clauses:                    916
% 3.94/0.99  inst_num_in_passive:                    371
% 3.94/0.99  inst_num_in_active:                     351
% 3.94/0.99  inst_num_in_unprocessed:                194
% 3.94/0.99  inst_num_of_loops:                      460
% 3.94/0.99  inst_num_of_learning_restarts:          0
% 3.94/0.99  inst_num_moves_active_passive:          107
% 3.94/0.99  inst_lit_activity:                      0
% 3.94/0.99  inst_lit_activity_moves:                1
% 3.94/0.99  inst_num_tautologies:                   0
% 3.94/0.99  inst_num_prop_implied:                  0
% 3.94/0.99  inst_num_existing_simplified:           0
% 3.94/0.99  inst_num_eq_res_simplified:             0
% 3.94/0.99  inst_num_child_elim:                    0
% 3.94/0.99  inst_num_of_dismatching_blockings:      97
% 3.94/0.99  inst_num_of_non_proper_insts:           675
% 3.94/0.99  inst_num_of_duplicates:                 0
% 3.94/0.99  inst_inst_num_from_inst_to_res:         0
% 3.94/0.99  inst_dismatching_checking_time:         0.
% 3.94/0.99  
% 3.94/0.99  ------ Resolution
% 3.94/0.99  
% 3.94/0.99  res_num_of_clauses:                     0
% 3.94/0.99  res_num_in_passive:                     0
% 3.94/0.99  res_num_in_active:                      0
% 3.94/0.99  res_num_of_loops:                       163
% 3.94/0.99  res_forward_subset_subsumed:            7
% 3.94/0.99  res_backward_subset_subsumed:           0
% 3.94/0.99  res_forward_subsumed:                   0
% 3.94/0.99  res_backward_subsumed:                  0
% 3.94/0.99  res_forward_subsumption_resolution:     0
% 3.94/0.99  res_backward_subsumption_resolution:    0
% 3.94/0.99  res_clause_to_clause_subsumption:       368
% 3.94/0.99  res_orphan_elimination:                 0
% 3.94/0.99  res_tautology_del:                      15
% 3.94/0.99  res_num_eq_res_simplified:              0
% 3.94/0.99  res_num_sel_changes:                    0
% 3.94/0.99  res_moves_from_active_to_pass:          0
% 3.94/0.99  
% 3.94/0.99  ------ Superposition
% 3.94/0.99  
% 3.94/0.99  sup_time_total:                         0.
% 3.94/0.99  sup_time_generating:                    0.
% 3.94/0.99  sup_time_sim_full:                      0.
% 3.94/0.99  sup_time_sim_immed:                     0.
% 3.94/0.99  
% 3.94/0.99  sup_num_of_clauses:                     131
% 3.94/0.99  sup_num_in_active:                      89
% 3.94/0.99  sup_num_in_passive:                     42
% 3.94/0.99  sup_num_of_loops:                       90
% 3.94/0.99  sup_fw_superposition:                   126
% 3.94/0.99  sup_bw_superposition:                   29
% 3.94/0.99  sup_immediate_simplified:               77
% 3.94/0.99  sup_given_eliminated:                   0
% 3.94/0.99  comparisons_done:                       0
% 3.94/0.99  comparisons_avoided:                    0
% 3.94/0.99  
% 3.94/0.99  ------ Simplifications
% 3.94/0.99  
% 3.94/0.99  
% 3.94/0.99  sim_fw_subset_subsumed:                 11
% 3.94/0.99  sim_bw_subset_subsumed:                 0
% 3.94/0.99  sim_fw_subsumed:                        10
% 3.94/0.99  sim_bw_subsumed:                        0
% 3.94/0.99  sim_fw_subsumption_res:                 0
% 3.94/0.99  sim_bw_subsumption_res:                 0
% 3.94/0.99  sim_tautology_del:                      4
% 3.94/0.99  sim_eq_tautology_del:                   12
% 3.94/0.99  sim_eq_res_simp:                        6
% 3.94/0.99  sim_fw_demodulated:                     20
% 3.94/0.99  sim_bw_demodulated:                     2
% 3.94/0.99  sim_light_normalised:                   50
% 3.94/0.99  sim_joinable_taut:                      0
% 3.94/0.99  sim_joinable_simp:                      0
% 3.94/0.99  sim_ac_normalised:                      0
% 3.94/0.99  sim_smt_subsumption:                    0
% 3.94/0.99  
%------------------------------------------------------------------------------
