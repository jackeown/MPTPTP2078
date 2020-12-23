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
% DateTime   : Thu Dec  3 12:21:33 EST 2020

% Result     : Theorem 6.67s
% Output     : CNFRefutation 6.67s
% Verified   : 
% Statistics : Number of formulae       :  200 (2196 expanded)
%              Number of clauses        :  134 ( 573 expanded)
%              Number of leaves         :   17 ( 869 expanded)
%              Depth                    :   23
%              Number of atoms          : 1175 (28985 expanded)
%              Number of equality atoms :  487 (6952 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f34])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f35,f46,f45,f44,f43,f42,f41])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f30])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f31])).

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
    inference(flattening,[],[f39])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f40])).

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
    inference(equality_resolution,[],[f64])).

fof(f13,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f32])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f75,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f40])).

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
    inference(equality_resolution,[],[f63])).

fof(f82,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_835,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1578,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_835])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_850,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1564,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_2165,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1578,c_1564])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_838,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1575,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_847,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1567,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_847])).

cnf(c_3030,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1575,c_1567])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1985,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
    inference(instantiation,[status(thm)],[c_847])).

cnf(c_2175,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_1985])).

cnf(c_4173,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3030,c_27,c_25,c_2175])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_841,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1572,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_841])).

cnf(c_3029,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1567])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1980,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
    inference(instantiation,[status(thm)],[c_847])).

cnf(c_2170,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(instantiation,[status(thm)],[c_1980])).

cnf(c_4120,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3029,c_24,c_22,c_2170])).

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
    inference(cnf_transformation,[],[f66])).

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
    inference(cnf_transformation,[],[f67])).

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
    inference(cnf_transformation,[],[f68])).

cnf(c_197,plain,
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

cnf(c_198,plain,
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
    inference(renaming,[status(thm)],[c_197])).

cnf(c_828,plain,
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
    inference(subtyping,[status(esa)],[c_198])).

cnf(c_1585,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_828])).

cnf(c_6537,plain,
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
    inference(superposition,[status(thm)],[c_4120,c_1585])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_39,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16792,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6537,c_36,c_39,c_45,c_46,c_47])).

cnf(c_16793,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_16792])).

cnf(c_16808,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4173,c_16793])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_37,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16992,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16808,c_37,c_42,c_43,c_44])).

cnf(c_16993,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_16992])).

cnf(c_17003,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2165,c_16993])).

cnf(c_7,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_28,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_511,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_28])).

cnf(c_512,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_511])).

cnf(c_514,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_512,c_32,c_30])).

cnf(c_827,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_514])).

cnf(c_1586,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_827])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_853,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | k3_xboole_0(X0_53,X1_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1561,plain,
    ( k3_xboole_0(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X0_53,X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_2576,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1586,c_1561])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_848,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1566,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_848])).

cnf(c_2524,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1566])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_851,plain,
    ( r1_xboole_0(X0_53,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1563,plain,
    ( r1_xboole_0(X0_53,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_852,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | r1_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1562,plain,
    ( r1_xboole_0(X0_53,X1_53) != iProver_top
    | r1_xboole_0(X1_53,X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_2665,plain,
    ( r1_xboole_0(k1_xboole_0,X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_1562])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_849,plain,
    ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1565,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_2886,plain,
    ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_53) != iProver_top ),
    inference(superposition,[status(thm)],[c_2665,c_1565])).

cnf(c_5096,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2524,c_2886])).

cnf(c_17004,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17003,c_2576,c_5096])).

cnf(c_845,plain,
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
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1569,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_3533,plain,
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
    inference(superposition,[status(thm)],[c_1569,c_1567])).

cnf(c_843,plain,
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
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1571,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_7406,plain,
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
    | v1_xboole_0(X3_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3533,c_1571])).

cnf(c_7410,plain,
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
    inference(superposition,[status(thm)],[c_1572,c_7406])).

cnf(c_7634,plain,
    ( v1_funct_1(X2_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7410,c_36,c_39,c_45,c_46])).

cnf(c_7635,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_7634])).

cnf(c_7649,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1575,c_7635])).

cnf(c_7953,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7649,c_37,c_42,c_43])).

cnf(c_7954,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_7953])).

cnf(c_7963,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_7954])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8041,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7963,c_35,c_38])).

cnf(c_17005,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17004,c_2165,c_8041])).

cnf(c_2525,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1575,c_1566])).

cnf(c_5097,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2525,c_2886])).

cnf(c_17006,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17005,c_2576,c_5097])).

cnf(c_17007,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17006])).

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

cnf(c_190,plain,
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

cnf(c_191,plain,
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
    inference(renaming,[status(thm)],[c_190])).

cnf(c_829,plain,
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
    inference(subtyping,[status(esa)],[c_191])).

cnf(c_1584,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_829])).

cnf(c_4572,plain,
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
    inference(superposition,[status(thm)],[c_4120,c_1584])).

cnf(c_9671,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4572,c_36,c_39,c_45,c_46,c_47])).

cnf(c_9672,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_9671])).

cnf(c_9687,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4173,c_9672])).

cnf(c_11709,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9687,c_37,c_42,c_43,c_44])).

cnf(c_11710,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_11709])).

cnf(c_11720,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2165,c_11710])).

cnf(c_11721,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11720,c_2576,c_5096])).

cnf(c_11722,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11721,c_2165,c_8041])).

cnf(c_11723,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11722,c_2576,c_5097])).

cnf(c_11724,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11723])).

cnf(c_21,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_842,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2415,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2165,c_842])).

cnf(c_2746,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2576,c_2415])).

cnf(c_4124,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4120,c_2746])).

cnf(c_4177,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4124,c_4173])).

cnf(c_8045,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8041,c_4177])).

cnf(c_8046,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_8045,c_8041])).

cnf(c_9666,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8046,c_5096,c_5097])).

cnf(c_9667,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_9666])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17007,c_11724,c_9667,c_40,c_38,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:43:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.67/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.67/1.49  
% 6.67/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.67/1.49  
% 6.67/1.49  ------  iProver source info
% 6.67/1.49  
% 6.67/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.67/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.67/1.49  git: non_committed_changes: false
% 6.67/1.49  git: last_make_outside_of_git: false
% 6.67/1.49  
% 6.67/1.49  ------ 
% 6.67/1.49  
% 6.67/1.49  ------ Input Options
% 6.67/1.49  
% 6.67/1.49  --out_options                           all
% 6.67/1.49  --tptp_safe_out                         true
% 6.67/1.49  --problem_path                          ""
% 6.67/1.49  --include_path                          ""
% 6.67/1.49  --clausifier                            res/vclausify_rel
% 6.67/1.49  --clausifier_options                    --mode clausify
% 6.67/1.49  --stdin                                 false
% 6.67/1.49  --stats_out                             all
% 6.67/1.49  
% 6.67/1.49  ------ General Options
% 6.67/1.49  
% 6.67/1.49  --fof                                   false
% 6.67/1.49  --time_out_real                         305.
% 6.67/1.49  --time_out_virtual                      -1.
% 6.67/1.49  --symbol_type_check                     false
% 6.67/1.49  --clausify_out                          false
% 6.67/1.49  --sig_cnt_out                           false
% 6.67/1.49  --trig_cnt_out                          false
% 6.67/1.49  --trig_cnt_out_tolerance                1.
% 6.67/1.49  --trig_cnt_out_sk_spl                   false
% 6.67/1.49  --abstr_cl_out                          false
% 6.67/1.49  
% 6.67/1.49  ------ Global Options
% 6.67/1.49  
% 6.67/1.49  --schedule                              default
% 6.67/1.49  --add_important_lit                     false
% 6.67/1.49  --prop_solver_per_cl                    1000
% 6.67/1.49  --min_unsat_core                        false
% 6.67/1.49  --soft_assumptions                      false
% 6.67/1.49  --soft_lemma_size                       3
% 6.67/1.49  --prop_impl_unit_size                   0
% 6.67/1.49  --prop_impl_unit                        []
% 6.67/1.49  --share_sel_clauses                     true
% 6.67/1.49  --reset_solvers                         false
% 6.67/1.49  --bc_imp_inh                            [conj_cone]
% 6.67/1.49  --conj_cone_tolerance                   3.
% 6.67/1.49  --extra_neg_conj                        none
% 6.67/1.49  --large_theory_mode                     true
% 6.67/1.49  --prolific_symb_bound                   200
% 6.67/1.49  --lt_threshold                          2000
% 6.67/1.49  --clause_weak_htbl                      true
% 6.67/1.49  --gc_record_bc_elim                     false
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing Options
% 6.67/1.49  
% 6.67/1.49  --preprocessing_flag                    true
% 6.67/1.49  --time_out_prep_mult                    0.1
% 6.67/1.49  --splitting_mode                        input
% 6.67/1.49  --splitting_grd                         true
% 6.67/1.49  --splitting_cvd                         false
% 6.67/1.49  --splitting_cvd_svl                     false
% 6.67/1.49  --splitting_nvd                         32
% 6.67/1.49  --sub_typing                            true
% 6.67/1.49  --prep_gs_sim                           true
% 6.67/1.49  --prep_unflatten                        true
% 6.67/1.49  --prep_res_sim                          true
% 6.67/1.49  --prep_upred                            true
% 6.67/1.49  --prep_sem_filter                       exhaustive
% 6.67/1.49  --prep_sem_filter_out                   false
% 6.67/1.49  --pred_elim                             true
% 6.67/1.49  --res_sim_input                         true
% 6.67/1.49  --eq_ax_congr_red                       true
% 6.67/1.49  --pure_diseq_elim                       true
% 6.67/1.49  --brand_transform                       false
% 6.67/1.49  --non_eq_to_eq                          false
% 6.67/1.49  --prep_def_merge                        true
% 6.67/1.49  --prep_def_merge_prop_impl              false
% 6.67/1.49  --prep_def_merge_mbd                    true
% 6.67/1.49  --prep_def_merge_tr_red                 false
% 6.67/1.49  --prep_def_merge_tr_cl                  false
% 6.67/1.49  --smt_preprocessing                     true
% 6.67/1.49  --smt_ac_axioms                         fast
% 6.67/1.49  --preprocessed_out                      false
% 6.67/1.49  --preprocessed_stats                    false
% 6.67/1.49  
% 6.67/1.49  ------ Abstraction refinement Options
% 6.67/1.49  
% 6.67/1.49  --abstr_ref                             []
% 6.67/1.49  --abstr_ref_prep                        false
% 6.67/1.49  --abstr_ref_until_sat                   false
% 6.67/1.49  --abstr_ref_sig_restrict                funpre
% 6.67/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.67/1.49  --abstr_ref_under                       []
% 6.67/1.49  
% 6.67/1.49  ------ SAT Options
% 6.67/1.49  
% 6.67/1.49  --sat_mode                              false
% 6.67/1.49  --sat_fm_restart_options                ""
% 6.67/1.49  --sat_gr_def                            false
% 6.67/1.49  --sat_epr_types                         true
% 6.67/1.49  --sat_non_cyclic_types                  false
% 6.67/1.49  --sat_finite_models                     false
% 6.67/1.49  --sat_fm_lemmas                         false
% 6.67/1.49  --sat_fm_prep                           false
% 6.67/1.49  --sat_fm_uc_incr                        true
% 6.67/1.49  --sat_out_model                         small
% 6.67/1.49  --sat_out_clauses                       false
% 6.67/1.49  
% 6.67/1.49  ------ QBF Options
% 6.67/1.49  
% 6.67/1.49  --qbf_mode                              false
% 6.67/1.49  --qbf_elim_univ                         false
% 6.67/1.49  --qbf_dom_inst                          none
% 6.67/1.49  --qbf_dom_pre_inst                      false
% 6.67/1.49  --qbf_sk_in                             false
% 6.67/1.49  --qbf_pred_elim                         true
% 6.67/1.49  --qbf_split                             512
% 6.67/1.49  
% 6.67/1.49  ------ BMC1 Options
% 6.67/1.49  
% 6.67/1.49  --bmc1_incremental                      false
% 6.67/1.49  --bmc1_axioms                           reachable_all
% 6.67/1.49  --bmc1_min_bound                        0
% 6.67/1.49  --bmc1_max_bound                        -1
% 6.67/1.49  --bmc1_max_bound_default                -1
% 6.67/1.49  --bmc1_symbol_reachability              true
% 6.67/1.49  --bmc1_property_lemmas                  false
% 6.67/1.49  --bmc1_k_induction                      false
% 6.67/1.49  --bmc1_non_equiv_states                 false
% 6.67/1.49  --bmc1_deadlock                         false
% 6.67/1.49  --bmc1_ucm                              false
% 6.67/1.49  --bmc1_add_unsat_core                   none
% 6.67/1.49  --bmc1_unsat_core_children              false
% 6.67/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.67/1.49  --bmc1_out_stat                         full
% 6.67/1.49  --bmc1_ground_init                      false
% 6.67/1.49  --bmc1_pre_inst_next_state              false
% 6.67/1.49  --bmc1_pre_inst_state                   false
% 6.67/1.49  --bmc1_pre_inst_reach_state             false
% 6.67/1.49  --bmc1_out_unsat_core                   false
% 6.67/1.49  --bmc1_aig_witness_out                  false
% 6.67/1.49  --bmc1_verbose                          false
% 6.67/1.49  --bmc1_dump_clauses_tptp                false
% 6.67/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.67/1.49  --bmc1_dump_file                        -
% 6.67/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.67/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.67/1.49  --bmc1_ucm_extend_mode                  1
% 6.67/1.49  --bmc1_ucm_init_mode                    2
% 6.67/1.49  --bmc1_ucm_cone_mode                    none
% 6.67/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.67/1.49  --bmc1_ucm_relax_model                  4
% 6.67/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.67/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.67/1.49  --bmc1_ucm_layered_model                none
% 6.67/1.49  --bmc1_ucm_max_lemma_size               10
% 6.67/1.49  
% 6.67/1.49  ------ AIG Options
% 6.67/1.49  
% 6.67/1.49  --aig_mode                              false
% 6.67/1.49  
% 6.67/1.49  ------ Instantiation Options
% 6.67/1.49  
% 6.67/1.49  --instantiation_flag                    true
% 6.67/1.49  --inst_sos_flag                         false
% 6.67/1.49  --inst_sos_phase                        true
% 6.67/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.67/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.67/1.49  --inst_lit_sel_side                     num_symb
% 6.67/1.49  --inst_solver_per_active                1400
% 6.67/1.49  --inst_solver_calls_frac                1.
% 6.67/1.49  --inst_passive_queue_type               priority_queues
% 6.67/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.67/1.49  --inst_passive_queues_freq              [25;2]
% 6.67/1.49  --inst_dismatching                      true
% 6.67/1.49  --inst_eager_unprocessed_to_passive     true
% 6.67/1.49  --inst_prop_sim_given                   true
% 6.67/1.49  --inst_prop_sim_new                     false
% 6.67/1.49  --inst_subs_new                         false
% 6.67/1.49  --inst_eq_res_simp                      false
% 6.67/1.49  --inst_subs_given                       false
% 6.67/1.49  --inst_orphan_elimination               true
% 6.67/1.49  --inst_learning_loop_flag               true
% 6.67/1.49  --inst_learning_start                   3000
% 6.67/1.49  --inst_learning_factor                  2
% 6.67/1.49  --inst_start_prop_sim_after_learn       3
% 6.67/1.49  --inst_sel_renew                        solver
% 6.67/1.49  --inst_lit_activity_flag                true
% 6.67/1.49  --inst_restr_to_given                   false
% 6.67/1.49  --inst_activity_threshold               500
% 6.67/1.49  --inst_out_proof                        true
% 6.67/1.49  
% 6.67/1.49  ------ Resolution Options
% 6.67/1.49  
% 6.67/1.49  --resolution_flag                       true
% 6.67/1.49  --res_lit_sel                           adaptive
% 6.67/1.49  --res_lit_sel_side                      none
% 6.67/1.49  --res_ordering                          kbo
% 6.67/1.49  --res_to_prop_solver                    active
% 6.67/1.49  --res_prop_simpl_new                    false
% 6.67/1.49  --res_prop_simpl_given                  true
% 6.67/1.49  --res_passive_queue_type                priority_queues
% 6.67/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.67/1.49  --res_passive_queues_freq               [15;5]
% 6.67/1.49  --res_forward_subs                      full
% 6.67/1.49  --res_backward_subs                     full
% 6.67/1.49  --res_forward_subs_resolution           true
% 6.67/1.49  --res_backward_subs_resolution          true
% 6.67/1.49  --res_orphan_elimination                true
% 6.67/1.49  --res_time_limit                        2.
% 6.67/1.49  --res_out_proof                         true
% 6.67/1.49  
% 6.67/1.49  ------ Superposition Options
% 6.67/1.49  
% 6.67/1.49  --superposition_flag                    true
% 6.67/1.49  --sup_passive_queue_type                priority_queues
% 6.67/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.67/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.67/1.49  --demod_completeness_check              fast
% 6.67/1.49  --demod_use_ground                      true
% 6.67/1.49  --sup_to_prop_solver                    passive
% 6.67/1.49  --sup_prop_simpl_new                    true
% 6.67/1.49  --sup_prop_simpl_given                  true
% 6.67/1.49  --sup_fun_splitting                     false
% 6.67/1.49  --sup_smt_interval                      50000
% 6.67/1.49  
% 6.67/1.49  ------ Superposition Simplification Setup
% 6.67/1.49  
% 6.67/1.49  --sup_indices_passive                   []
% 6.67/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.67/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_full_bw                           [BwDemod]
% 6.67/1.49  --sup_immed_triv                        [TrivRules]
% 6.67/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.67/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_immed_bw_main                     []
% 6.67/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.67/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.49  
% 6.67/1.49  ------ Combination Options
% 6.67/1.49  
% 6.67/1.49  --comb_res_mult                         3
% 6.67/1.49  --comb_sup_mult                         2
% 6.67/1.49  --comb_inst_mult                        10
% 6.67/1.49  
% 6.67/1.49  ------ Debug Options
% 6.67/1.49  
% 6.67/1.49  --dbg_backtrace                         false
% 6.67/1.49  --dbg_dump_prop_clauses                 false
% 6.67/1.49  --dbg_dump_prop_clauses_file            -
% 6.67/1.49  --dbg_out_stat                          false
% 6.67/1.49  ------ Parsing...
% 6.67/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.67/1.49  ------ Proving...
% 6.67/1.49  ------ Problem Properties 
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  clauses                                 29
% 6.67/1.49  conjectures                             13
% 6.67/1.49  EPR                                     11
% 6.67/1.49  Horn                                    22
% 6.67/1.49  unary                                   14
% 6.67/1.49  binary                                  5
% 6.67/1.49  lits                                    122
% 6.67/1.49  lits eq                                 15
% 6.67/1.49  fd_pure                                 0
% 6.67/1.49  fd_pseudo                               0
% 6.67/1.49  fd_cond                                 0
% 6.67/1.49  fd_pseudo_cond                          1
% 6.67/1.49  AC symbols                              0
% 6.67/1.49  
% 6.67/1.49  ------ Schedule dynamic 5 is on 
% 6.67/1.49  
% 6.67/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  ------ 
% 6.67/1.49  Current options:
% 6.67/1.49  ------ 
% 6.67/1.49  
% 6.67/1.49  ------ Input Options
% 6.67/1.49  
% 6.67/1.49  --out_options                           all
% 6.67/1.49  --tptp_safe_out                         true
% 6.67/1.49  --problem_path                          ""
% 6.67/1.49  --include_path                          ""
% 6.67/1.49  --clausifier                            res/vclausify_rel
% 6.67/1.49  --clausifier_options                    --mode clausify
% 6.67/1.49  --stdin                                 false
% 6.67/1.49  --stats_out                             all
% 6.67/1.49  
% 6.67/1.49  ------ General Options
% 6.67/1.49  
% 6.67/1.49  --fof                                   false
% 6.67/1.49  --time_out_real                         305.
% 6.67/1.49  --time_out_virtual                      -1.
% 6.67/1.49  --symbol_type_check                     false
% 6.67/1.49  --clausify_out                          false
% 6.67/1.49  --sig_cnt_out                           false
% 6.67/1.49  --trig_cnt_out                          false
% 6.67/1.49  --trig_cnt_out_tolerance                1.
% 6.67/1.49  --trig_cnt_out_sk_spl                   false
% 6.67/1.49  --abstr_cl_out                          false
% 6.67/1.49  
% 6.67/1.49  ------ Global Options
% 6.67/1.49  
% 6.67/1.49  --schedule                              default
% 6.67/1.49  --add_important_lit                     false
% 6.67/1.49  --prop_solver_per_cl                    1000
% 6.67/1.49  --min_unsat_core                        false
% 6.67/1.49  --soft_assumptions                      false
% 6.67/1.49  --soft_lemma_size                       3
% 6.67/1.49  --prop_impl_unit_size                   0
% 6.67/1.49  --prop_impl_unit                        []
% 6.67/1.49  --share_sel_clauses                     true
% 6.67/1.49  --reset_solvers                         false
% 6.67/1.49  --bc_imp_inh                            [conj_cone]
% 6.67/1.49  --conj_cone_tolerance                   3.
% 6.67/1.49  --extra_neg_conj                        none
% 6.67/1.49  --large_theory_mode                     true
% 6.67/1.49  --prolific_symb_bound                   200
% 6.67/1.49  --lt_threshold                          2000
% 6.67/1.49  --clause_weak_htbl                      true
% 6.67/1.49  --gc_record_bc_elim                     false
% 6.67/1.49  
% 6.67/1.49  ------ Preprocessing Options
% 6.67/1.49  
% 6.67/1.49  --preprocessing_flag                    true
% 6.67/1.49  --time_out_prep_mult                    0.1
% 6.67/1.49  --splitting_mode                        input
% 6.67/1.49  --splitting_grd                         true
% 6.67/1.49  --splitting_cvd                         false
% 6.67/1.49  --splitting_cvd_svl                     false
% 6.67/1.49  --splitting_nvd                         32
% 6.67/1.49  --sub_typing                            true
% 6.67/1.49  --prep_gs_sim                           true
% 6.67/1.49  --prep_unflatten                        true
% 6.67/1.49  --prep_res_sim                          true
% 6.67/1.49  --prep_upred                            true
% 6.67/1.49  --prep_sem_filter                       exhaustive
% 6.67/1.49  --prep_sem_filter_out                   false
% 6.67/1.49  --pred_elim                             true
% 6.67/1.49  --res_sim_input                         true
% 6.67/1.49  --eq_ax_congr_red                       true
% 6.67/1.49  --pure_diseq_elim                       true
% 6.67/1.49  --brand_transform                       false
% 6.67/1.49  --non_eq_to_eq                          false
% 6.67/1.49  --prep_def_merge                        true
% 6.67/1.49  --prep_def_merge_prop_impl              false
% 6.67/1.49  --prep_def_merge_mbd                    true
% 6.67/1.49  --prep_def_merge_tr_red                 false
% 6.67/1.49  --prep_def_merge_tr_cl                  false
% 6.67/1.49  --smt_preprocessing                     true
% 6.67/1.49  --smt_ac_axioms                         fast
% 6.67/1.49  --preprocessed_out                      false
% 6.67/1.49  --preprocessed_stats                    false
% 6.67/1.49  
% 6.67/1.49  ------ Abstraction refinement Options
% 6.67/1.49  
% 6.67/1.49  --abstr_ref                             []
% 6.67/1.49  --abstr_ref_prep                        false
% 6.67/1.49  --abstr_ref_until_sat                   false
% 6.67/1.49  --abstr_ref_sig_restrict                funpre
% 6.67/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.67/1.49  --abstr_ref_under                       []
% 6.67/1.49  
% 6.67/1.49  ------ SAT Options
% 6.67/1.49  
% 6.67/1.49  --sat_mode                              false
% 6.67/1.49  --sat_fm_restart_options                ""
% 6.67/1.49  --sat_gr_def                            false
% 6.67/1.49  --sat_epr_types                         true
% 6.67/1.49  --sat_non_cyclic_types                  false
% 6.67/1.49  --sat_finite_models                     false
% 6.67/1.49  --sat_fm_lemmas                         false
% 6.67/1.49  --sat_fm_prep                           false
% 6.67/1.49  --sat_fm_uc_incr                        true
% 6.67/1.49  --sat_out_model                         small
% 6.67/1.49  --sat_out_clauses                       false
% 6.67/1.49  
% 6.67/1.49  ------ QBF Options
% 6.67/1.49  
% 6.67/1.49  --qbf_mode                              false
% 6.67/1.49  --qbf_elim_univ                         false
% 6.67/1.49  --qbf_dom_inst                          none
% 6.67/1.49  --qbf_dom_pre_inst                      false
% 6.67/1.49  --qbf_sk_in                             false
% 6.67/1.49  --qbf_pred_elim                         true
% 6.67/1.49  --qbf_split                             512
% 6.67/1.49  
% 6.67/1.49  ------ BMC1 Options
% 6.67/1.49  
% 6.67/1.49  --bmc1_incremental                      false
% 6.67/1.49  --bmc1_axioms                           reachable_all
% 6.67/1.49  --bmc1_min_bound                        0
% 6.67/1.49  --bmc1_max_bound                        -1
% 6.67/1.49  --bmc1_max_bound_default                -1
% 6.67/1.49  --bmc1_symbol_reachability              true
% 6.67/1.49  --bmc1_property_lemmas                  false
% 6.67/1.49  --bmc1_k_induction                      false
% 6.67/1.49  --bmc1_non_equiv_states                 false
% 6.67/1.49  --bmc1_deadlock                         false
% 6.67/1.49  --bmc1_ucm                              false
% 6.67/1.49  --bmc1_add_unsat_core                   none
% 6.67/1.49  --bmc1_unsat_core_children              false
% 6.67/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.67/1.49  --bmc1_out_stat                         full
% 6.67/1.49  --bmc1_ground_init                      false
% 6.67/1.49  --bmc1_pre_inst_next_state              false
% 6.67/1.49  --bmc1_pre_inst_state                   false
% 6.67/1.49  --bmc1_pre_inst_reach_state             false
% 6.67/1.49  --bmc1_out_unsat_core                   false
% 6.67/1.49  --bmc1_aig_witness_out                  false
% 6.67/1.49  --bmc1_verbose                          false
% 6.67/1.49  --bmc1_dump_clauses_tptp                false
% 6.67/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.67/1.49  --bmc1_dump_file                        -
% 6.67/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.67/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.67/1.49  --bmc1_ucm_extend_mode                  1
% 6.67/1.49  --bmc1_ucm_init_mode                    2
% 6.67/1.49  --bmc1_ucm_cone_mode                    none
% 6.67/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.67/1.49  --bmc1_ucm_relax_model                  4
% 6.67/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.67/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.67/1.49  --bmc1_ucm_layered_model                none
% 6.67/1.49  --bmc1_ucm_max_lemma_size               10
% 6.67/1.49  
% 6.67/1.49  ------ AIG Options
% 6.67/1.49  
% 6.67/1.49  --aig_mode                              false
% 6.67/1.49  
% 6.67/1.49  ------ Instantiation Options
% 6.67/1.49  
% 6.67/1.49  --instantiation_flag                    true
% 6.67/1.49  --inst_sos_flag                         false
% 6.67/1.49  --inst_sos_phase                        true
% 6.67/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.67/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.67/1.49  --inst_lit_sel_side                     none
% 6.67/1.49  --inst_solver_per_active                1400
% 6.67/1.49  --inst_solver_calls_frac                1.
% 6.67/1.49  --inst_passive_queue_type               priority_queues
% 6.67/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.67/1.49  --inst_passive_queues_freq              [25;2]
% 6.67/1.49  --inst_dismatching                      true
% 6.67/1.49  --inst_eager_unprocessed_to_passive     true
% 6.67/1.49  --inst_prop_sim_given                   true
% 6.67/1.49  --inst_prop_sim_new                     false
% 6.67/1.49  --inst_subs_new                         false
% 6.67/1.49  --inst_eq_res_simp                      false
% 6.67/1.49  --inst_subs_given                       false
% 6.67/1.49  --inst_orphan_elimination               true
% 6.67/1.49  --inst_learning_loop_flag               true
% 6.67/1.49  --inst_learning_start                   3000
% 6.67/1.49  --inst_learning_factor                  2
% 6.67/1.49  --inst_start_prop_sim_after_learn       3
% 6.67/1.49  --inst_sel_renew                        solver
% 6.67/1.49  --inst_lit_activity_flag                true
% 6.67/1.49  --inst_restr_to_given                   false
% 6.67/1.49  --inst_activity_threshold               500
% 6.67/1.49  --inst_out_proof                        true
% 6.67/1.49  
% 6.67/1.49  ------ Resolution Options
% 6.67/1.49  
% 6.67/1.49  --resolution_flag                       false
% 6.67/1.49  --res_lit_sel                           adaptive
% 6.67/1.49  --res_lit_sel_side                      none
% 6.67/1.49  --res_ordering                          kbo
% 6.67/1.49  --res_to_prop_solver                    active
% 6.67/1.49  --res_prop_simpl_new                    false
% 6.67/1.49  --res_prop_simpl_given                  true
% 6.67/1.49  --res_passive_queue_type                priority_queues
% 6.67/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.67/1.49  --res_passive_queues_freq               [15;5]
% 6.67/1.49  --res_forward_subs                      full
% 6.67/1.49  --res_backward_subs                     full
% 6.67/1.49  --res_forward_subs_resolution           true
% 6.67/1.49  --res_backward_subs_resolution          true
% 6.67/1.49  --res_orphan_elimination                true
% 6.67/1.49  --res_time_limit                        2.
% 6.67/1.49  --res_out_proof                         true
% 6.67/1.49  
% 6.67/1.49  ------ Superposition Options
% 6.67/1.49  
% 6.67/1.49  --superposition_flag                    true
% 6.67/1.49  --sup_passive_queue_type                priority_queues
% 6.67/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.67/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.67/1.49  --demod_completeness_check              fast
% 6.67/1.49  --demod_use_ground                      true
% 6.67/1.49  --sup_to_prop_solver                    passive
% 6.67/1.49  --sup_prop_simpl_new                    true
% 6.67/1.49  --sup_prop_simpl_given                  true
% 6.67/1.49  --sup_fun_splitting                     false
% 6.67/1.49  --sup_smt_interval                      50000
% 6.67/1.49  
% 6.67/1.49  ------ Superposition Simplification Setup
% 6.67/1.49  
% 6.67/1.49  --sup_indices_passive                   []
% 6.67/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.67/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.67/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_full_bw                           [BwDemod]
% 6.67/1.49  --sup_immed_triv                        [TrivRules]
% 6.67/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.67/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_immed_bw_main                     []
% 6.67/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.67/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.67/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.67/1.49  
% 6.67/1.49  ------ Combination Options
% 6.67/1.49  
% 6.67/1.49  --comb_res_mult                         3
% 6.67/1.49  --comb_sup_mult                         2
% 6.67/1.49  --comb_inst_mult                        10
% 6.67/1.49  
% 6.67/1.49  ------ Debug Options
% 6.67/1.49  
% 6.67/1.49  --dbg_backtrace                         false
% 6.67/1.49  --dbg_dump_prop_clauses                 false
% 6.67/1.49  --dbg_dump_prop_clauses_file            -
% 6.67/1.49  --dbg_out_stat                          false
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  ------ Proving...
% 6.67/1.49  
% 6.67/1.49  
% 6.67/1.49  % SZS status Theorem for theBenchmark.p
% 6.67/1.49  
% 6.67/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.67/1.49  
% 6.67/1.49  fof(f14,conjecture,(
% 6.67/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f15,negated_conjecture,(
% 6.67/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.67/1.49    inference(negated_conjecture,[],[f14])).
% 6.67/1.49  
% 6.67/1.49  fof(f34,plain,(
% 6.67/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.67/1.49    inference(ennf_transformation,[],[f15])).
% 6.67/1.49  
% 6.67/1.49  fof(f35,plain,(
% 6.67/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.67/1.49    inference(flattening,[],[f34])).
% 6.67/1.49  
% 6.67/1.49  fof(f46,plain,(
% 6.67/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 6.67/1.49    introduced(choice_axiom,[])).
% 6.67/1.49  
% 6.67/1.49  fof(f45,plain,(
% 6.67/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 6.67/1.49    introduced(choice_axiom,[])).
% 6.67/1.49  
% 6.67/1.49  fof(f44,plain,(
% 6.67/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 6.67/1.49    introduced(choice_axiom,[])).
% 6.67/1.49  
% 6.67/1.49  fof(f43,plain,(
% 6.67/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 6.67/1.49    introduced(choice_axiom,[])).
% 6.67/1.49  
% 6.67/1.49  fof(f42,plain,(
% 6.67/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 6.67/1.49    introduced(choice_axiom,[])).
% 6.67/1.49  
% 6.67/1.49  fof(f41,plain,(
% 6.67/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 6.67/1.49    introduced(choice_axiom,[])).
% 6.67/1.49  
% 6.67/1.49  fof(f47,plain,(
% 6.67/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 6.67/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f35,f46,f45,f44,f43,f42,f41])).
% 6.67/1.49  
% 6.67/1.49  fof(f74,plain,(
% 6.67/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f4,axiom,(
% 6.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f18,plain,(
% 6.67/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.67/1.49    inference(ennf_transformation,[],[f4])).
% 6.67/1.49  
% 6.67/1.49  fof(f52,plain,(
% 6.67/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.67/1.49    inference(cnf_transformation,[],[f18])).
% 6.67/1.49  
% 6.67/1.49  fof(f78,plain,(
% 6.67/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f11,axiom,(
% 6.67/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f28,plain,(
% 6.67/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.67/1.49    inference(ennf_transformation,[],[f11])).
% 6.67/1.49  
% 6.67/1.49  fof(f29,plain,(
% 6.67/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.67/1.49    inference(flattening,[],[f28])).
% 6.67/1.49  
% 6.67/1.49  fof(f62,plain,(
% 6.67/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f29])).
% 6.67/1.49  
% 6.67/1.49  fof(f76,plain,(
% 6.67/1.49    v1_funct_1(sK4)),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f81,plain,(
% 6.67/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f79,plain,(
% 6.67/1.49    v1_funct_1(sK5)),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f12,axiom,(
% 6.67/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f30,plain,(
% 6.67/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.67/1.49    inference(ennf_transformation,[],[f12])).
% 6.67/1.49  
% 6.67/1.49  fof(f31,plain,(
% 6.67/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.67/1.49    inference(flattening,[],[f30])).
% 6.67/1.49  
% 6.67/1.49  fof(f39,plain,(
% 6.67/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.67/1.49    inference(nnf_transformation,[],[f31])).
% 6.67/1.49  
% 6.67/1.49  fof(f40,plain,(
% 6.67/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.67/1.49    inference(flattening,[],[f39])).
% 6.67/1.49  
% 6.67/1.49  fof(f64,plain,(
% 6.67/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f40])).
% 6.67/1.49  
% 6.67/1.49  fof(f86,plain,(
% 6.67/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.67/1.49    inference(equality_resolution,[],[f64])).
% 6.67/1.49  
% 6.67/1.49  fof(f13,axiom,(
% 6.67/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f32,plain,(
% 6.67/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.67/1.49    inference(ennf_transformation,[],[f13])).
% 6.67/1.49  
% 6.67/1.49  fof(f33,plain,(
% 6.67/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.67/1.49    inference(flattening,[],[f32])).
% 6.67/1.49  
% 6.67/1.49  fof(f66,plain,(
% 6.67/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f33])).
% 6.67/1.49  
% 6.67/1.49  fof(f67,plain,(
% 6.67/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f33])).
% 6.67/1.49  
% 6.67/1.49  fof(f68,plain,(
% 6.67/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f33])).
% 6.67/1.49  
% 6.67/1.49  fof(f70,plain,(
% 6.67/1.49    ~v1_xboole_0(sK1)),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f73,plain,(
% 6.67/1.49    ~v1_xboole_0(sK3)),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f80,plain,(
% 6.67/1.49    v1_funct_2(sK5,sK3,sK1)),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f71,plain,(
% 6.67/1.49    ~v1_xboole_0(sK2)),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f77,plain,(
% 6.67/1.49    v1_funct_2(sK4,sK2,sK1)),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f6,axiom,(
% 6.67/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f20,plain,(
% 6.67/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.67/1.49    inference(ennf_transformation,[],[f6])).
% 6.67/1.49  
% 6.67/1.49  fof(f21,plain,(
% 6.67/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.67/1.49    inference(flattening,[],[f20])).
% 6.67/1.49  
% 6.67/1.49  fof(f37,plain,(
% 6.67/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.67/1.49    inference(nnf_transformation,[],[f21])).
% 6.67/1.49  
% 6.67/1.49  fof(f54,plain,(
% 6.67/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f37])).
% 6.67/1.49  
% 6.67/1.49  fof(f75,plain,(
% 6.67/1.49    r1_subset_1(sK2,sK3)),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f1,axiom,(
% 6.67/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f36,plain,(
% 6.67/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.67/1.49    inference(nnf_transformation,[],[f1])).
% 6.67/1.49  
% 6.67/1.49  fof(f48,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f36])).
% 6.67/1.49  
% 6.67/1.49  fof(f7,axiom,(
% 6.67/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f22,plain,(
% 6.67/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.67/1.49    inference(ennf_transformation,[],[f7])).
% 6.67/1.49  
% 6.67/1.49  fof(f56,plain,(
% 6.67/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.67/1.49    inference(cnf_transformation,[],[f22])).
% 6.67/1.49  
% 6.67/1.49  fof(f3,axiom,(
% 6.67/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f51,plain,(
% 6.67/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f3])).
% 6.67/1.49  
% 6.67/1.49  fof(f2,axiom,(
% 6.67/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f17,plain,(
% 6.67/1.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 6.67/1.49    inference(ennf_transformation,[],[f2])).
% 6.67/1.49  
% 6.67/1.49  fof(f50,plain,(
% 6.67/1.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f17])).
% 6.67/1.49  
% 6.67/1.49  fof(f5,axiom,(
% 6.67/1.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 6.67/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.67/1.49  
% 6.67/1.49  fof(f19,plain,(
% 6.67/1.49    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 6.67/1.49    inference(ennf_transformation,[],[f5])).
% 6.67/1.49  
% 6.67/1.49  fof(f53,plain,(
% 6.67/1.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f19])).
% 6.67/1.49  
% 6.67/1.49  fof(f69,plain,(
% 6.67/1.49    ~v1_xboole_0(sK0)),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f72,plain,(
% 6.67/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  fof(f63,plain,(
% 6.67/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.67/1.49    inference(cnf_transformation,[],[f40])).
% 6.67/1.49  
% 6.67/1.49  fof(f87,plain,(
% 6.67/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.67/1.49    inference(equality_resolution,[],[f63])).
% 6.67/1.49  
% 6.67/1.49  fof(f82,plain,(
% 6.67/1.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 6.67/1.49    inference(cnf_transformation,[],[f47])).
% 6.67/1.49  
% 6.67/1.49  cnf(c_29,negated_conjecture,
% 6.67/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 6.67/1.49      inference(cnf_transformation,[],[f74]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_835,negated_conjecture,
% 6.67/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 6.67/1.49      inference(subtyping,[status(esa)],[c_29]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1578,plain,
% 6.67/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.67/1.49      inference(predicate_to_equality,[status(thm)],[c_835]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_4,plain,
% 6.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.67/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 6.67/1.49      inference(cnf_transformation,[],[f52]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_850,plain,
% 6.67/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 6.67/1.49      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 6.67/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1564,plain,
% 6.67/1.49      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 6.67/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 6.67/1.49      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_2165,plain,
% 6.67/1.49      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 6.67/1.49      inference(superposition,[status(thm)],[c_1578,c_1564]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_25,negated_conjecture,
% 6.67/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 6.67/1.49      inference(cnf_transformation,[],[f78]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_838,negated_conjecture,
% 6.67/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 6.67/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1575,plain,
% 6.67/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 6.67/1.49      inference(predicate_to_equality,[status(thm)],[c_838]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_14,plain,
% 6.67/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.49      | ~ v1_funct_1(X0)
% 6.67/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.67/1.49      inference(cnf_transformation,[],[f62]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_847,plain,
% 6.67/1.49      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 6.67/1.49      | ~ v1_funct_1(X0_53)
% 6.67/1.49      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 6.67/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_1567,plain,
% 6.67/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 6.67/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 6.67/1.49      | v1_funct_1(X2_53) != iProver_top ),
% 6.67/1.49      inference(predicate_to_equality,[status(thm)],[c_847]) ).
% 6.67/1.49  
% 6.67/1.49  cnf(c_3030,plain,
% 6.67/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 6.67/1.49      | v1_funct_1(sK4) != iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_1575,c_1567]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_27,negated_conjecture,
% 6.67/1.50      ( v1_funct_1(sK4) ),
% 6.67/1.50      inference(cnf_transformation,[],[f76]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1985,plain,
% 6.67/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 6.67/1.50      | ~ v1_funct_1(sK4)
% 6.67/1.50      | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
% 6.67/1.50      inference(instantiation,[status(thm)],[c_847]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_2175,plain,
% 6.67/1.50      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.67/1.50      | ~ v1_funct_1(sK4)
% 6.67/1.50      | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 6.67/1.50      inference(instantiation,[status(thm)],[c_1985]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_4173,plain,
% 6.67/1.50      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_3030,c_27,c_25,c_2175]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_22,negated_conjecture,
% 6.67/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 6.67/1.50      inference(cnf_transformation,[],[f81]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_841,negated_conjecture,
% 6.67/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_22]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1572,plain,
% 6.67/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_841]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_3029,plain,
% 6.67/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 6.67/1.50      | v1_funct_1(sK5) != iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_1572,c_1567]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_24,negated_conjecture,
% 6.67/1.50      ( v1_funct_1(sK5) ),
% 6.67/1.50      inference(cnf_transformation,[],[f79]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1980,plain,
% 6.67/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 6.67/1.50      | ~ v1_funct_1(sK5)
% 6.67/1.50      | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
% 6.67/1.50      inference(instantiation,[status(thm)],[c_847]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_2170,plain,
% 6.67/1.50      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 6.67/1.50      | ~ v1_funct_1(sK5)
% 6.67/1.50      | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 6.67/1.50      inference(instantiation,[status(thm)],[c_1980]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_4120,plain,
% 6.67/1.50      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_3029,c_24,c_22,c_2170]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_16,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.67/1.50      | ~ v1_funct_2(X3,X4,X2)
% 6.67/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.67/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.67/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.67/1.50      | ~ v1_funct_1(X0)
% 6.67/1.50      | ~ v1_funct_1(X3)
% 6.67/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.67/1.50      | v1_xboole_0(X5)
% 6.67/1.50      | v1_xboole_0(X2)
% 6.67/1.50      | v1_xboole_0(X4)
% 6.67/1.50      | v1_xboole_0(X1)
% 6.67/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.67/1.50      inference(cnf_transformation,[],[f86]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_20,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.67/1.50      | ~ v1_funct_2(X3,X4,X2)
% 6.67/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.67/1.50      | ~ v1_funct_1(X0)
% 6.67/1.50      | ~ v1_funct_1(X3)
% 6.67/1.50      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.67/1.50      | v1_xboole_0(X5)
% 6.67/1.50      | v1_xboole_0(X2)
% 6.67/1.50      | v1_xboole_0(X4)
% 6.67/1.50      | v1_xboole_0(X1) ),
% 6.67/1.50      inference(cnf_transformation,[],[f66]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_19,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.67/1.50      | ~ v1_funct_2(X3,X4,X2)
% 6.67/1.50      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.67/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.67/1.50      | ~ v1_funct_1(X0)
% 6.67/1.50      | ~ v1_funct_1(X3)
% 6.67/1.50      | v1_xboole_0(X5)
% 6.67/1.50      | v1_xboole_0(X2)
% 6.67/1.50      | v1_xboole_0(X4)
% 6.67/1.50      | v1_xboole_0(X1) ),
% 6.67/1.50      inference(cnf_transformation,[],[f67]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_18,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.67/1.50      | ~ v1_funct_2(X3,X4,X2)
% 6.67/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.67/1.50      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.67/1.50      | ~ v1_funct_1(X0)
% 6.67/1.50      | ~ v1_funct_1(X3)
% 6.67/1.50      | v1_xboole_0(X5)
% 6.67/1.50      | v1_xboole_0(X2)
% 6.67/1.50      | v1_xboole_0(X4)
% 6.67/1.50      | v1_xboole_0(X1) ),
% 6.67/1.50      inference(cnf_transformation,[],[f68]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_197,plain,
% 6.67/1.50      ( ~ v1_funct_1(X3)
% 6.67/1.50      | ~ v1_funct_1(X0)
% 6.67/1.50      | ~ v1_funct_2(X3,X4,X2)
% 6.67/1.50      | ~ v1_funct_2(X0,X1,X2)
% 6.67/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.67/1.50      | v1_xboole_0(X5)
% 6.67/1.50      | v1_xboole_0(X2)
% 6.67/1.50      | v1_xboole_0(X4)
% 6.67/1.50      | v1_xboole_0(X1)
% 6.67/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_16,c_20,c_19,c_18]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_198,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.67/1.50      | ~ v1_funct_2(X3,X4,X2)
% 6.67/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.67/1.50      | ~ v1_funct_1(X0)
% 6.67/1.50      | ~ v1_funct_1(X3)
% 6.67/1.50      | v1_xboole_0(X1)
% 6.67/1.50      | v1_xboole_0(X2)
% 6.67/1.50      | v1_xboole_0(X4)
% 6.67/1.50      | v1_xboole_0(X5)
% 6.67/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.67/1.50      inference(renaming,[status(thm)],[c_197]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_828,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 6.67/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 6.67/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 6.67/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 6.67/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 6.67/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 6.67/1.50      | ~ v1_funct_1(X0_53)
% 6.67/1.50      | ~ v1_funct_1(X3_53)
% 6.67/1.50      | v1_xboole_0(X2_53)
% 6.67/1.50      | v1_xboole_0(X1_53)
% 6.67/1.50      | v1_xboole_0(X4_53)
% 6.67/1.50      | v1_xboole_0(X5_53)
% 6.67/1.50      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_198]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1585,plain,
% 6.67/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 6.67/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 6.67/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 6.67/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 6.67/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 6.67/1.50      | v1_funct_1(X2_53) != iProver_top
% 6.67/1.50      | v1_funct_1(X5_53) != iProver_top
% 6.67/1.50      | v1_xboole_0(X3_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X1_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X4_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_828]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_6537,plain,
% 6.67/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 6.67/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 6.67/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.67/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | v1_funct_1(X1_53) != iProver_top
% 6.67/1.50      | v1_funct_1(sK5) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X2_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(sK1) = iProver_top
% 6.67/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_4120,c_1585]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_33,negated_conjecture,
% 6.67/1.50      ( ~ v1_xboole_0(sK1) ),
% 6.67/1.50      inference(cnf_transformation,[],[f70]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_36,plain,
% 6.67/1.50      ( v1_xboole_0(sK1) != iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_30,negated_conjecture,
% 6.67/1.50      ( ~ v1_xboole_0(sK3) ),
% 6.67/1.50      inference(cnf_transformation,[],[f73]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_39,plain,
% 6.67/1.50      ( v1_xboole_0(sK3) != iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_45,plain,
% 6.67/1.50      ( v1_funct_1(sK5) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_23,negated_conjecture,
% 6.67/1.50      ( v1_funct_2(sK5,sK3,sK1) ),
% 6.67/1.50      inference(cnf_transformation,[],[f80]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_46,plain,
% 6.67/1.50      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_47,plain,
% 6.67/1.50      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_16792,plain,
% 6.67/1.50      ( v1_funct_1(X1_53) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 6.67/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 6.67/1.50      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 6.67/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X2_53) = iProver_top ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_6537,c_36,c_39,c_45,c_46,c_47]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_16793,plain,
% 6.67/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 6.67/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 6.67/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | v1_funct_1(X1_53) != iProver_top
% 6.67/1.50      | v1_xboole_0(X2_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 6.67/1.50      inference(renaming,[status(thm)],[c_16792]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_16808,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.67/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 6.67/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.67/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | v1_funct_1(sK4) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_4173,c_16793]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_32,negated_conjecture,
% 6.67/1.50      ( ~ v1_xboole_0(sK2) ),
% 6.67/1.50      inference(cnf_transformation,[],[f71]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_37,plain,
% 6.67/1.50      ( v1_xboole_0(sK2) != iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_42,plain,
% 6.67/1.50      ( v1_funct_1(sK4) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_26,negated_conjecture,
% 6.67/1.50      ( v1_funct_2(sK4,sK2,sK1) ),
% 6.67/1.50      inference(cnf_transformation,[],[f77]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_43,plain,
% 6.67/1.50      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_44,plain,
% 6.67/1.50      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_16992,plain,
% 6.67/1.50      ( v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.67/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_16808,c_37,c_42,c_43,c_44]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_16993,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.67/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 6.67/1.50      inference(renaming,[status(thm)],[c_16992]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_17003,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.67/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_2165,c_16993]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_7,plain,
% 6.67/1.50      ( ~ r1_subset_1(X0,X1)
% 6.67/1.50      | r1_xboole_0(X0,X1)
% 6.67/1.50      | v1_xboole_0(X0)
% 6.67/1.50      | v1_xboole_0(X1) ),
% 6.67/1.50      inference(cnf_transformation,[],[f54]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_28,negated_conjecture,
% 6.67/1.50      ( r1_subset_1(sK2,sK3) ),
% 6.67/1.50      inference(cnf_transformation,[],[f75]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_511,plain,
% 6.67/1.50      ( r1_xboole_0(X0,X1)
% 6.67/1.50      | v1_xboole_0(X0)
% 6.67/1.50      | v1_xboole_0(X1)
% 6.67/1.50      | sK3 != X1
% 6.67/1.50      | sK2 != X0 ),
% 6.67/1.50      inference(resolution_lifted,[status(thm)],[c_7,c_28]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_512,plain,
% 6.67/1.50      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 6.67/1.50      inference(unflattening,[status(thm)],[c_511]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_514,plain,
% 6.67/1.50      ( r1_xboole_0(sK2,sK3) ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_512,c_32,c_30]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_827,plain,
% 6.67/1.50      ( r1_xboole_0(sK2,sK3) ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_514]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1586,plain,
% 6.67/1.50      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_827]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1,plain,
% 6.67/1.50      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 6.67/1.50      inference(cnf_transformation,[],[f48]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_853,plain,
% 6.67/1.50      ( ~ r1_xboole_0(X0_53,X1_53)
% 6.67/1.50      | k3_xboole_0(X0_53,X1_53) = k1_xboole_0 ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1561,plain,
% 6.67/1.50      ( k3_xboole_0(X0_53,X1_53) = k1_xboole_0
% 6.67/1.50      | r1_xboole_0(X0_53,X1_53) != iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_2576,plain,
% 6.67/1.50      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_1586,c_1561]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_8,plain,
% 6.67/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.50      | v1_relat_1(X0) ),
% 6.67/1.50      inference(cnf_transformation,[],[f56]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_848,plain,
% 6.67/1.50      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 6.67/1.50      | v1_relat_1(X0_53) ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1566,plain,
% 6.67/1.50      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 6.67/1.50      | v1_relat_1(X0_53) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_848]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_2524,plain,
% 6.67/1.50      ( v1_relat_1(sK5) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_1572,c_1566]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_3,plain,
% 6.67/1.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 6.67/1.50      inference(cnf_transformation,[],[f51]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_851,plain,
% 6.67/1.50      ( r1_xboole_0(X0_53,k1_xboole_0) ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1563,plain,
% 6.67/1.50      ( r1_xboole_0(X0_53,k1_xboole_0) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_2,plain,
% 6.67/1.50      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 6.67/1.50      inference(cnf_transformation,[],[f50]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_852,plain,
% 6.67/1.50      ( ~ r1_xboole_0(X0_53,X1_53) | r1_xboole_0(X1_53,X0_53) ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_2]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1562,plain,
% 6.67/1.50      ( r1_xboole_0(X0_53,X1_53) != iProver_top
% 6.67/1.50      | r1_xboole_0(X1_53,X0_53) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_2665,plain,
% 6.67/1.50      ( r1_xboole_0(k1_xboole_0,X0_53) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_1563,c_1562]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_5,plain,
% 6.67/1.50      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 6.67/1.50      | ~ v1_relat_1(X1)
% 6.67/1.50      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 6.67/1.50      inference(cnf_transformation,[],[f53]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_849,plain,
% 6.67/1.50      ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
% 6.67/1.50      | ~ v1_relat_1(X1_53)
% 6.67/1.50      | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_5]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1565,plain,
% 6.67/1.50      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 6.67/1.50      | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
% 6.67/1.50      | v1_relat_1(X0_53) != iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_2886,plain,
% 6.67/1.50      ( k7_relat_1(X0_53,k1_xboole_0) = k1_xboole_0
% 6.67/1.50      | v1_relat_1(X0_53) != iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_2665,c_1565]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_5096,plain,
% 6.67/1.50      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_2524,c_2886]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_17004,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.67/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(light_normalisation,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_17003,c_2576,c_5096]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_845,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 6.67/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 6.67/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 6.67/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 6.67/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 6.67/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 6.67/1.50      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
% 6.67/1.50      | ~ v1_funct_1(X0_53)
% 6.67/1.50      | ~ v1_funct_1(X3_53)
% 6.67/1.50      | v1_xboole_0(X2_53)
% 6.67/1.50      | v1_xboole_0(X1_53)
% 6.67/1.50      | v1_xboole_0(X4_53)
% 6.67/1.50      | v1_xboole_0(X5_53) ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_18]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1569,plain,
% 6.67/1.50      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 6.67/1.50      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 6.67/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 6.67/1.50      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 6.67/1.50      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 6.67/1.50      | v1_funct_1(X0_53) != iProver_top
% 6.67/1.50      | v1_funct_1(X3_53) != iProver_top
% 6.67/1.50      | v1_xboole_0(X5_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X2_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X4_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X1_53) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_3533,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 6.67/1.50      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 6.67/1.50      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 6.67/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 6.67/1.50      | v1_funct_1(X5_53) != iProver_top
% 6.67/1.50      | v1_funct_1(X4_53) != iProver_top
% 6.67/1.50      | v1_funct_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53)) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X3_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X1_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X2_53) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_1569,c_1567]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_843,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 6.67/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 6.67/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 6.67/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 6.67/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 6.67/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 6.67/1.50      | ~ v1_funct_1(X0_53)
% 6.67/1.50      | ~ v1_funct_1(X3_53)
% 6.67/1.50      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
% 6.67/1.50      | v1_xboole_0(X2_53)
% 6.67/1.50      | v1_xboole_0(X1_53)
% 6.67/1.50      | v1_xboole_0(X4_53)
% 6.67/1.50      | v1_xboole_0(X5_53) ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_20]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1571,plain,
% 6.67/1.50      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 6.67/1.50      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 6.67/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 6.67/1.50      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 6.67/1.50      | v1_funct_1(X0_53) != iProver_top
% 6.67/1.50      | v1_funct_1(X3_53) != iProver_top
% 6.67/1.50      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 6.67/1.50      | v1_xboole_0(X5_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X2_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X4_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X1_53) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_7406,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 6.67/1.50      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 6.67/1.50      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 6.67/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 6.67/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 6.67/1.50      | v1_funct_1(X5_53) != iProver_top
% 6.67/1.50      | v1_funct_1(X4_53) != iProver_top
% 6.67/1.50      | v1_xboole_0(X2_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X1_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X3_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 6.67/1.50      inference(forward_subsumption_resolution,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_3533,c_1571]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_7410,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 6.67/1.50      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 6.67/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | v1_funct_1(X2_53) != iProver_top
% 6.67/1.50      | v1_funct_1(sK5) != iProver_top
% 6.67/1.50      | v1_xboole_0(X1_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(sK1) = iProver_top
% 6.67/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_1572,c_7406]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_7634,plain,
% 6.67/1.50      ( v1_funct_1(X2_53) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 6.67/1.50      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 6.67/1.50      | v1_xboole_0(X1_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_7410,c_36,c_39,c_45,c_46]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_7635,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 6.67/1.50      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | v1_funct_1(X2_53) != iProver_top
% 6.67/1.50      | v1_xboole_0(X1_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 6.67/1.50      inference(renaming,[status(thm)],[c_7634]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_7649,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 6.67/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | v1_funct_1(sK4) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_1575,c_7635]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_7953,plain,
% 6.67/1.50      ( v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_7649,c_37,c_42,c_43]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_7954,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 6.67/1.50      inference(renaming,[status(thm)],[c_7953]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_7963,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_1578,c_7954]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_34,negated_conjecture,
% 6.67/1.50      ( ~ v1_xboole_0(sK0) ),
% 6.67/1.50      inference(cnf_transformation,[],[f69]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_35,plain,
% 6.67/1.50      ( v1_xboole_0(sK0) != iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_31,negated_conjecture,
% 6.67/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 6.67/1.50      inference(cnf_transformation,[],[f72]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_38,plain,
% 6.67/1.50      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_8041,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_7963,c_35,c_38]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_17005,plain,
% 6.67/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.67/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(demodulation,[status(thm)],[c_17004,c_2165,c_8041]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_2525,plain,
% 6.67/1.50      ( v1_relat_1(sK4) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_1575,c_1566]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_5097,plain,
% 6.67/1.50      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_2525,c_2886]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_17006,plain,
% 6.67/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.67/1.50      | k1_xboole_0 != k1_xboole_0
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(light_normalisation,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_17005,c_2576,c_5097]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_17007,plain,
% 6.67/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(equality_resolution_simp,[status(thm)],[c_17006]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_17,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.67/1.50      | ~ v1_funct_2(X3,X4,X2)
% 6.67/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.67/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.67/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.67/1.50      | ~ v1_funct_1(X0)
% 6.67/1.50      | ~ v1_funct_1(X3)
% 6.67/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.67/1.50      | v1_xboole_0(X5)
% 6.67/1.50      | v1_xboole_0(X2)
% 6.67/1.50      | v1_xboole_0(X4)
% 6.67/1.50      | v1_xboole_0(X1)
% 6.67/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.67/1.50      inference(cnf_transformation,[],[f87]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_190,plain,
% 6.67/1.50      ( ~ v1_funct_1(X3)
% 6.67/1.50      | ~ v1_funct_1(X0)
% 6.67/1.50      | ~ v1_funct_2(X3,X4,X2)
% 6.67/1.50      | ~ v1_funct_2(X0,X1,X2)
% 6.67/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.67/1.50      | v1_xboole_0(X5)
% 6.67/1.50      | v1_xboole_0(X2)
% 6.67/1.50      | v1_xboole_0(X4)
% 6.67/1.50      | v1_xboole_0(X1)
% 6.67/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_17,c_20,c_19,c_18]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_191,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 6.67/1.50      | ~ v1_funct_2(X3,X4,X2)
% 6.67/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.67/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.67/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.67/1.50      | ~ v1_funct_1(X0)
% 6.67/1.50      | ~ v1_funct_1(X3)
% 6.67/1.50      | v1_xboole_0(X1)
% 6.67/1.50      | v1_xboole_0(X2)
% 6.67/1.50      | v1_xboole_0(X4)
% 6.67/1.50      | v1_xboole_0(X5)
% 6.67/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.67/1.50      inference(renaming,[status(thm)],[c_190]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_829,plain,
% 6.67/1.50      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 6.67/1.50      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 6.67/1.50      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 6.67/1.50      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 6.67/1.50      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 6.67/1.50      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 6.67/1.50      | ~ v1_funct_1(X0_53)
% 6.67/1.50      | ~ v1_funct_1(X3_53)
% 6.67/1.50      | v1_xboole_0(X2_53)
% 6.67/1.50      | v1_xboole_0(X1_53)
% 6.67/1.50      | v1_xboole_0(X4_53)
% 6.67/1.50      | v1_xboole_0(X5_53)
% 6.67/1.50      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_191]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_1584,plain,
% 6.67/1.50      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 6.67/1.50      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 6.67/1.50      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 6.67/1.50      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 6.67/1.50      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 6.67/1.50      | v1_funct_1(X2_53) != iProver_top
% 6.67/1.50      | v1_funct_1(X5_53) != iProver_top
% 6.67/1.50      | v1_xboole_0(X3_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X1_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X4_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_829]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_4572,plain,
% 6.67/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 6.67/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 6.67/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.67/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | v1_funct_1(X1_53) != iProver_top
% 6.67/1.50      | v1_funct_1(sK5) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X2_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(sK1) = iProver_top
% 6.67/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_4120,c_1584]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_9671,plain,
% 6.67/1.50      ( v1_funct_1(X1_53) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 6.67/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 6.67/1.50      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 6.67/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X2_53) = iProver_top ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_4572,c_36,c_39,c_45,c_46,c_47]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_9672,plain,
% 6.67/1.50      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 6.67/1.50      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 6.67/1.50      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 6.67/1.50      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 6.67/1.50      | v1_funct_1(X1_53) != iProver_top
% 6.67/1.50      | v1_xboole_0(X2_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 6.67/1.50      inference(renaming,[status(thm)],[c_9671]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_9687,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.67/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 6.67/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.67/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | v1_funct_1(sK4) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_4173,c_9672]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_11709,plain,
% 6.67/1.50      ( v1_xboole_0(X0_53) = iProver_top
% 6.67/1.50      | k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.67/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 6.67/1.50      inference(global_propositional_subsumption,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_9687,c_37,c_42,c_43,c_44]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_11710,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.67/1.50      | k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3))
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 6.67/1.50      | v1_xboole_0(X0_53) = iProver_top ),
% 6.67/1.50      inference(renaming,[status(thm)],[c_11709]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_11720,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.67/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(superposition,[status(thm)],[c_2165,c_11710]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_11721,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.67/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(light_normalisation,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_11720,c_2576,c_5096]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_11722,plain,
% 6.67/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.67/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(demodulation,[status(thm)],[c_11721,c_2165,c_8041]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_11723,plain,
% 6.67/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.67/1.50      | k1_xboole_0 != k1_xboole_0
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(light_normalisation,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_11722,c_2576,c_5097]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_11724,plain,
% 6.67/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.67/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.67/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 6.67/1.50      inference(equality_resolution_simp,[status(thm)],[c_11723]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_21,negated_conjecture,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.67/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.67/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 6.67/1.50      inference(cnf_transformation,[],[f82]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_842,negated_conjecture,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.67/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.67/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 6.67/1.50      inference(subtyping,[status(esa)],[c_21]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_2415,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.67/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.67/1.50      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 6.67/1.50      inference(demodulation,[status(thm)],[c_2165,c_842]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_2746,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.67/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.67/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 6.67/1.50      inference(demodulation,[status(thm)],[c_2576,c_2415]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_4124,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.67/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.67/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 6.67/1.50      inference(demodulation,[status(thm)],[c_4120,c_2746]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_4177,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.67/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.67/1.50      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 6.67/1.50      inference(demodulation,[status(thm)],[c_4124,c_4173]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_8045,plain,
% 6.67/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.67/1.50      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.67/1.50      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 6.67/1.50      inference(demodulation,[status(thm)],[c_8041,c_4177]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_8046,plain,
% 6.67/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.67/1.50      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.67/1.50      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 6.67/1.50      inference(demodulation,[status(thm)],[c_8045,c_8041]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_9666,plain,
% 6.67/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.67/1.50      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.67/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 6.67/1.50      inference(light_normalisation,[status(thm)],[c_8046,c_5096,c_5097]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_9667,plain,
% 6.67/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.67/1.50      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 6.67/1.50      inference(equality_resolution_simp,[status(thm)],[c_9666]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(c_40,plain,
% 6.67/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.67/1.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.67/1.50  
% 6.67/1.50  cnf(contradiction,plain,
% 6.67/1.50      ( $false ),
% 6.67/1.50      inference(minisat,
% 6.67/1.50                [status(thm)],
% 6.67/1.50                [c_17007,c_11724,c_9667,c_40,c_38,c_35]) ).
% 6.67/1.50  
% 6.67/1.50  
% 6.67/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 6.67/1.50  
% 6.67/1.50  ------                               Statistics
% 6.67/1.50  
% 6.67/1.50  ------ General
% 6.67/1.50  
% 6.67/1.50  abstr_ref_over_cycles:                  0
% 6.67/1.50  abstr_ref_under_cycles:                 0
% 6.67/1.50  gc_basic_clause_elim:                   0
% 6.67/1.50  forced_gc_time:                         0
% 6.67/1.50  parsing_time:                           0.012
% 6.67/1.50  unif_index_cands_time:                  0.
% 6.67/1.50  unif_index_add_time:                    0.
% 6.67/1.50  orderings_time:                         0.
% 6.67/1.50  out_proof_time:                         0.015
% 6.67/1.50  total_time:                             0.838
% 6.67/1.50  num_of_symbols:                         58
% 6.67/1.50  num_of_terms:                           31873
% 6.67/1.50  
% 6.67/1.50  ------ Preprocessing
% 6.67/1.50  
% 6.67/1.50  num_of_splits:                          0
% 6.67/1.50  num_of_split_atoms:                     0
% 6.67/1.50  num_of_reused_defs:                     0
% 6.67/1.50  num_eq_ax_congr_red:                    21
% 6.67/1.50  num_of_sem_filtered_clauses:            1
% 6.67/1.50  num_of_subtypes:                        2
% 6.67/1.50  monotx_restored_types:                  0
% 6.67/1.50  sat_num_of_epr_types:                   0
% 6.67/1.50  sat_num_of_non_cyclic_types:            0
% 6.67/1.50  sat_guarded_non_collapsed_types:        1
% 6.67/1.50  num_pure_diseq_elim:                    0
% 6.67/1.50  simp_replaced_by:                       0
% 6.67/1.50  res_preprocessed:                       150
% 6.67/1.50  prep_upred:                             0
% 6.67/1.50  prep_unflattend:                        8
% 6.67/1.50  smt_new_axioms:                         0
% 6.67/1.50  pred_elim_cands:                        6
% 6.67/1.50  pred_elim:                              3
% 6.67/1.50  pred_elim_cl:                           5
% 6.67/1.50  pred_elim_cycles:                       6
% 6.67/1.50  merged_defs:                            8
% 6.67/1.50  merged_defs_ncl:                        0
% 6.67/1.50  bin_hyper_res:                          8
% 6.67/1.50  prep_cycles:                            4
% 6.67/1.50  pred_elim_time:                         0.004
% 6.67/1.50  splitting_time:                         0.
% 6.67/1.50  sem_filter_time:                        0.
% 6.67/1.50  monotx_time:                            0.
% 6.67/1.50  subtype_inf_time:                       0.013
% 6.67/1.50  
% 6.67/1.50  ------ Problem properties
% 6.67/1.50  
% 6.67/1.50  clauses:                                29
% 6.67/1.50  conjectures:                            13
% 6.67/1.50  epr:                                    11
% 6.67/1.50  horn:                                   22
% 6.67/1.50  ground:                                 14
% 6.67/1.50  unary:                                  14
% 6.67/1.50  binary:                                 5
% 6.67/1.50  lits:                                   122
% 6.67/1.50  lits_eq:                                15
% 6.67/1.50  fd_pure:                                0
% 6.67/1.50  fd_pseudo:                              0
% 6.67/1.50  fd_cond:                                0
% 6.67/1.50  fd_pseudo_cond:                         1
% 6.67/1.50  ac_symbols:                             0
% 6.67/1.50  
% 6.67/1.50  ------ Propositional Solver
% 6.67/1.50  
% 6.67/1.50  prop_solver_calls:                      29
% 6.67/1.50  prop_fast_solver_calls:                 2753
% 6.67/1.50  smt_solver_calls:                       0
% 6.67/1.50  smt_fast_solver_calls:                  0
% 6.67/1.50  prop_num_of_clauses:                    6765
% 6.67/1.50  prop_preprocess_simplified:             13558
% 6.67/1.50  prop_fo_subsumed:                       204
% 6.67/1.50  prop_solver_time:                       0.
% 6.67/1.50  smt_solver_time:                        0.
% 6.67/1.50  smt_fast_solver_time:                   0.
% 6.67/1.50  prop_fast_solver_time:                  0.
% 6.67/1.50  prop_unsat_core_time:                   0.
% 6.67/1.50  
% 6.67/1.50  ------ QBF
% 6.67/1.50  
% 6.67/1.50  qbf_q_res:                              0
% 6.67/1.50  qbf_num_tautologies:                    0
% 6.67/1.50  qbf_prep_cycles:                        0
% 6.67/1.50  
% 6.67/1.50  ------ BMC1
% 6.67/1.50  
% 6.67/1.50  bmc1_current_bound:                     -1
% 6.67/1.50  bmc1_last_solved_bound:                 -1
% 6.67/1.50  bmc1_unsat_core_size:                   -1
% 6.67/1.50  bmc1_unsat_core_parents_size:           -1
% 6.67/1.50  bmc1_merge_next_fun:                    0
% 6.67/1.50  bmc1_unsat_core_clauses_time:           0.
% 6.67/1.50  
% 6.67/1.50  ------ Instantiation
% 6.67/1.50  
% 6.67/1.50  inst_num_of_clauses:                    1570
% 6.67/1.50  inst_num_in_passive:                    823
% 6.67/1.50  inst_num_in_active:                     665
% 6.67/1.50  inst_num_in_unprocessed:                82
% 6.67/1.50  inst_num_of_loops:                      680
% 6.67/1.50  inst_num_of_learning_restarts:          0
% 6.67/1.50  inst_num_moves_active_passive:          11
% 6.67/1.50  inst_lit_activity:                      0
% 6.67/1.50  inst_lit_activity_moves:                0
% 6.67/1.50  inst_num_tautologies:                   0
% 6.67/1.50  inst_num_prop_implied:                  0
% 6.67/1.50  inst_num_existing_simplified:           0
% 6.67/1.50  inst_num_eq_res_simplified:             0
% 6.67/1.50  inst_num_child_elim:                    0
% 6.67/1.50  inst_num_of_dismatching_blockings:      177
% 6.67/1.50  inst_num_of_non_proper_insts:           1230
% 6.67/1.50  inst_num_of_duplicates:                 0
% 6.67/1.50  inst_inst_num_from_inst_to_res:         0
% 6.67/1.50  inst_dismatching_checking_time:         0.
% 6.67/1.50  
% 6.67/1.50  ------ Resolution
% 6.67/1.50  
% 6.67/1.50  res_num_of_clauses:                     0
% 6.67/1.50  res_num_in_passive:                     0
% 6.67/1.50  res_num_in_active:                      0
% 6.67/1.50  res_num_of_loops:                       154
% 6.67/1.50  res_forward_subset_subsumed:            46
% 6.67/1.50  res_backward_subset_subsumed:           0
% 6.67/1.50  res_forward_subsumed:                   0
% 6.67/1.50  res_backward_subsumed:                  0
% 6.67/1.50  res_forward_subsumption_resolution:     1
% 6.67/1.50  res_backward_subsumption_resolution:    0
% 6.67/1.50  res_clause_to_clause_subsumption:       1690
% 6.67/1.50  res_orphan_elimination:                 0
% 6.67/1.50  res_tautology_del:                      44
% 6.67/1.50  res_num_eq_res_simplified:              0
% 6.67/1.50  res_num_sel_changes:                    0
% 6.67/1.50  res_moves_from_active_to_pass:          0
% 6.67/1.50  
% 6.67/1.50  ------ Superposition
% 6.67/1.50  
% 6.67/1.50  sup_time_total:                         0.
% 6.67/1.50  sup_time_generating:                    0.
% 6.67/1.50  sup_time_sim_full:                      0.
% 6.67/1.50  sup_time_sim_immed:                     0.
% 6.67/1.50  
% 6.67/1.50  sup_num_of_clauses:                     254
% 6.67/1.50  sup_num_in_active:                      130
% 6.67/1.50  sup_num_in_passive:                     124
% 6.67/1.50  sup_num_of_loops:                       134
% 6.67/1.50  sup_fw_superposition:                   204
% 6.67/1.50  sup_bw_superposition:                   66
% 6.67/1.50  sup_immediate_simplified:               122
% 6.67/1.50  sup_given_eliminated:                   0
% 6.67/1.50  comparisons_done:                       0
% 6.67/1.50  comparisons_avoided:                    0
% 6.67/1.50  
% 6.67/1.50  ------ Simplifications
% 6.67/1.50  
% 6.67/1.50  
% 6.67/1.50  sim_fw_subset_subsumed:                 0
% 6.67/1.50  sim_bw_subset_subsumed:                 2
% 6.67/1.50  sim_fw_subsumed:                        6
% 6.67/1.50  sim_bw_subsumed:                        8
% 6.67/1.50  sim_fw_subsumption_res:                 3
% 6.67/1.50  sim_bw_subsumption_res:                 0
% 6.67/1.50  sim_tautology_del:                      0
% 6.67/1.50  sim_eq_tautology_del:                   6
% 6.67/1.50  sim_eq_res_simp:                        6
% 6.67/1.50  sim_fw_demodulated:                     74
% 6.67/1.50  sim_bw_demodulated:                     5
% 6.67/1.50  sim_light_normalised:                   58
% 6.67/1.50  sim_joinable_taut:                      0
% 6.67/1.50  sim_joinable_simp:                      0
% 6.67/1.50  sim_ac_normalised:                      0
% 6.67/1.50  sim_smt_subsumption:                    0
% 6.67/1.50  
%------------------------------------------------------------------------------
