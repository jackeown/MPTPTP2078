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
% DateTime   : Thu Dec  3 12:21:22 EST 2020

% Result     : Theorem 7.03s
% Output     : CNFRefutation 7.03s
% Verified   : 
% Statistics : Number of formulae       :  259 (6809 expanded)
%              Number of clauses        :  177 (1744 expanded)
%              Number of leaves         :   21 (2240 expanded)
%              Depth                    :   27
%              Number of atoms          : 1437 (69083 expanded)
%              Number of equality atoms :  618 (15457 expanded)
%              Maximal formula depth    :   25 (   6 average)
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
    inference(ennf_transformation,[],[f16])).

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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f49,f48,f47,f46,f45,f44])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f35])).

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
    inference(flattening,[],[f42])).

fof(f67,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f89,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f69,plain,(
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

fof(f70,plain,(
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

fof(f71,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f74,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f78,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
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
    inference(equality_resolution,[],[f66])).

fof(f85,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_757,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1291,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_775,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1274,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_775])).

cnf(c_1927,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1291,c_1274])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_764,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1284,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_770,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1279,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_770])).

cnf(c_2306,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1279])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1703,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_1879,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(instantiation,[status(thm)],[c_1703])).

cnf(c_2511,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2306,c_24,c_22,c_1879])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_761,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1287,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_2307,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_1279])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1708,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
    inference(instantiation,[status(thm)],[c_770])).

cnf(c_1884,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_2517,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2307,c_27,c_25,c_1884])).

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
    inference(cnf_transformation,[],[f89])).

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
    inference(cnf_transformation,[],[f69])).

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
    inference(cnf_transformation,[],[f70])).

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
    inference(cnf_transformation,[],[f71])).

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

cnf(c_750,plain,
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
    inference(subtyping,[status(esa)],[c_192])).

cnf(c_1298,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_774,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1275,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_xboole_0(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_774])).

cnf(c_1507,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1298,c_1275])).

cnf(c_6452,plain,
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
    inference(superposition,[status(thm)],[c_2517,c_1507])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_36,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17951,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6452,c_36,c_37,c_42,c_43,c_44])).

cnf(c_17952,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
    | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_17951])).

cnf(c_17965,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2511,c_17952])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_45,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_46,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_18343,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17965,c_39,c_45,c_46,c_47])).

cnf(c_18353,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1927,c_18343])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_13,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_360,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_9,c_13])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_13,c_9,c_8])).

cnf(c_365,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_364])).

cnf(c_435,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_10,c_365])).

cnf(c_439,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_13,c_10,c_9,c_8])).

cnf(c_440,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_439])).

cnf(c_749,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X2_53)
    | k1_relat_1(X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_440])).

cnf(c_1299,plain,
    ( k1_relat_1(X0_53) = X1_53
    | v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_2634,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1299])).

cnf(c_1693,plain,
    ( ~ v1_funct_2(sK5,X0_53,X1_53)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_53)
    | k1_relat_1(sK5) = X0_53 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1873,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_3135,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2634,c_33,c_24,c_23,c_22,c_1873])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_776,plain,
    ( k3_xboole_0(X0_53,X1_53) = k3_xboole_0(X1_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_771,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1278,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_2249,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1278])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_773,plain,
    ( ~ v1_relat_1(X0_53)
    | k7_relat_1(X0_53,k3_xboole_0(k1_relat_1(X0_53),X1_53)) = k7_relat_1(X0_53,X1_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1276,plain,
    ( k7_relat_1(X0_53,k3_xboole_0(k1_relat_1(X0_53),X1_53)) = k7_relat_1(X0_53,X1_53)
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_2372,plain,
    ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0_53)) = k7_relat_1(sK5,X0_53) ),
    inference(superposition,[status(thm)],[c_2249,c_1276])).

cnf(c_2655,plain,
    ( k7_relat_1(sK5,k3_xboole_0(X0_53,k1_relat_1(sK5))) = k7_relat_1(sK5,X0_53) ),
    inference(superposition,[status(thm)],[c_776,c_2372])).

cnf(c_3138,plain,
    ( k7_relat_1(sK5,k3_xboole_0(X0_53,sK3)) = k7_relat_1(sK5,X0_53) ),
    inference(demodulation,[status(thm)],[c_3135,c_2655])).

cnf(c_2635,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_1299])).

cnf(c_1698,plain,
    ( ~ v1_funct_2(sK4,X0_53,X1_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_53)
    | k1_relat_1(sK4) = X0_53 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1876,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_1698])).

cnf(c_3263,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2635,c_33,c_27,c_26,c_25,c_1876])).

cnf(c_2250,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_1278])).

cnf(c_2376,plain,
    ( k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0_53)) = k7_relat_1(sK4,X0_53) ),
    inference(superposition,[status(thm)],[c_2250,c_1276])).

cnf(c_3267,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK2,X0_53)) = k7_relat_1(sK4,X0_53) ),
    inference(demodulation,[status(thm)],[c_3263,c_2376])).

cnf(c_28,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_758,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1290,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_6,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_468,plain,
    ( ~ r1_subset_1(X0,X1)
    | ~ v1_relat_1(X2)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X0 != X3
    | k7_relat_1(X2,X3) = k1_xboole_0
    | k1_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_469,plain,
    ( ~ r1_subset_1(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(X1))
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_468])).

cnf(c_748,plain,
    ( ~ r1_subset_1(X0_53,k1_relat_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(k1_relat_1(X1_53))
    | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_469])).

cnf(c_1300,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | r1_subset_1(X1_53,k1_relat_1(X0_53)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(k1_relat_1(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_3796,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(k1_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3135,c_1300])).

cnf(c_3814,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3796,c_3135])).

cnf(c_1619,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1620,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1619])).

cnf(c_4286,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3814,c_39,c_47,c_1620])).

cnf(c_4287,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK3) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_4286])).

cnf(c_4295,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_4287])).

cnf(c_41,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3824,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0
    | r1_subset_1(sK2,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3814])).

cnf(c_4298,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4295,c_37,c_39,c_41,c_47,c_1620,c_3824])).

cnf(c_768,plain,
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

cnf(c_1281,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_1452,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1281,c_1275])).

cnf(c_3953,plain,
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
    inference(superposition,[status(thm)],[c_1452,c_1279])).

cnf(c_766,plain,
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

cnf(c_1283,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_1400,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1283,c_1275])).

cnf(c_8827,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_3953,c_1400])).

cnf(c_8831,plain,
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
    inference(superposition,[status(thm)],[c_1284,c_8827])).

cnf(c_8930,plain,
    ( v1_funct_1(X2_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8831,c_36,c_39,c_45,c_46])).

cnf(c_8931,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_8930])).

cnf(c_8944,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1287,c_8931])).

cnf(c_9323,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8944,c_37,c_42,c_43])).

cnf(c_9332,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_9323])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9337,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9332,c_38])).

cnf(c_18354,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_18353,c_1927,c_3138,c_3267,c_4298,c_9337])).

cnf(c_7,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_772,plain,
    ( ~ r1_subset_1(X0_53,X1_53)
    | r1_subset_1(X1_53,X0_53)
    | v1_xboole_0(X0_53)
    | v1_xboole_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1277,plain,
    ( r1_subset_1(X0_53,X1_53) != iProver_top
    | r1_subset_1(X1_53,X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_772])).

cnf(c_2300,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_1277])).

cnf(c_1639,plain,
    ( r1_subset_1(sK3,sK2)
    | ~ r1_subset_1(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_1640,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | r1_subset_1(sK2,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1639])).

cnf(c_2583,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2300,c_37,c_39,c_41,c_1640])).

cnf(c_3797,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3263,c_1300])).

cnf(c_3803,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3797,c_3263])).

cnf(c_1622,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_1623,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1622])).

cnf(c_4236,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3803,c_37,c_44,c_1623])).

cnf(c_4237,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_subset_1(X0_53,sK2) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_4236])).

cnf(c_4245,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2583,c_4237])).

cnf(c_4248,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4245,c_39])).

cnf(c_18355,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18354,c_4248])).

cnf(c_18356,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_18355])).

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
    inference(cnf_transformation,[],[f90])).

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

cnf(c_751,plain,
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
    inference(subtyping,[status(esa)],[c_185])).

cnf(c_1297,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_1479,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1297,c_1275])).

cnf(c_4734,plain,
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
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2511,c_1479])).

cnf(c_15368,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4734,c_36,c_39,c_45,c_46,c_47])).

cnf(c_15369,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_15368])).

cnf(c_15388,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_1927,c_15369])).

cnf(c_15397,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,X0_53)
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15388,c_1927,c_3138])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_15579,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,X0_53)
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15397,c_40])).

cnf(c_15580,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,X0_53)
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_15579])).

cnf(c_15593,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,sK2)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_15580])).

cnf(c_15681,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15593,c_4298])).

cnf(c_15682,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_15681,c_3267,c_4248,c_9337])).

cnf(c_15683,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15682])).

cnf(c_21,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_765,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2092,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_1927,c_765])).

cnf(c_2515,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2511,c_2092])).

cnf(c_2578,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2515,c_2517])).

cnf(c_3274,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,sK2) ),
    inference(demodulation,[status(thm)],[c_3138,c_2578])).

cnf(c_3671,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2) ),
    inference(demodulation,[status(thm)],[c_3274,c_3267])).

cnf(c_4251,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4248,c_3671])).

cnf(c_4351,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4251,c_37,c_39,c_41,c_47,c_1620,c_3824])).

cnf(c_4352,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_4351])).

cnf(c_9341,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_9337,c_4352])).

cnf(c_9342,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_9341,c_9337])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18356,c_15683,c_9342,c_44,c_43,c_42,c_40,c_38,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:31:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.03/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.03/1.48  
% 7.03/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.03/1.48  
% 7.03/1.48  ------  iProver source info
% 7.03/1.48  
% 7.03/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.03/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.03/1.48  git: non_committed_changes: false
% 7.03/1.48  git: last_make_outside_of_git: false
% 7.03/1.48  
% 7.03/1.48  ------ 
% 7.03/1.48  
% 7.03/1.48  ------ Input Options
% 7.03/1.48  
% 7.03/1.48  --out_options                           all
% 7.03/1.48  --tptp_safe_out                         true
% 7.03/1.48  --problem_path                          ""
% 7.03/1.48  --include_path                          ""
% 7.03/1.48  --clausifier                            res/vclausify_rel
% 7.03/1.48  --clausifier_options                    --mode clausify
% 7.03/1.48  --stdin                                 false
% 7.03/1.48  --stats_out                             all
% 7.03/1.48  
% 7.03/1.48  ------ General Options
% 7.03/1.48  
% 7.03/1.48  --fof                                   false
% 7.03/1.48  --time_out_real                         305.
% 7.03/1.48  --time_out_virtual                      -1.
% 7.03/1.48  --symbol_type_check                     false
% 7.03/1.48  --clausify_out                          false
% 7.03/1.48  --sig_cnt_out                           false
% 7.03/1.48  --trig_cnt_out                          false
% 7.03/1.48  --trig_cnt_out_tolerance                1.
% 7.03/1.48  --trig_cnt_out_sk_spl                   false
% 7.03/1.48  --abstr_cl_out                          false
% 7.03/1.48  
% 7.03/1.48  ------ Global Options
% 7.03/1.48  
% 7.03/1.48  --schedule                              default
% 7.03/1.48  --add_important_lit                     false
% 7.03/1.48  --prop_solver_per_cl                    1000
% 7.03/1.48  --min_unsat_core                        false
% 7.03/1.48  --soft_assumptions                      false
% 7.03/1.48  --soft_lemma_size                       3
% 7.03/1.48  --prop_impl_unit_size                   0
% 7.03/1.48  --prop_impl_unit                        []
% 7.03/1.48  --share_sel_clauses                     true
% 7.03/1.48  --reset_solvers                         false
% 7.03/1.48  --bc_imp_inh                            [conj_cone]
% 7.03/1.48  --conj_cone_tolerance                   3.
% 7.03/1.48  --extra_neg_conj                        none
% 7.03/1.48  --large_theory_mode                     true
% 7.03/1.48  --prolific_symb_bound                   200
% 7.03/1.48  --lt_threshold                          2000
% 7.03/1.48  --clause_weak_htbl                      true
% 7.03/1.48  --gc_record_bc_elim                     false
% 7.03/1.48  
% 7.03/1.48  ------ Preprocessing Options
% 7.03/1.48  
% 7.03/1.48  --preprocessing_flag                    true
% 7.03/1.48  --time_out_prep_mult                    0.1
% 7.03/1.48  --splitting_mode                        input
% 7.03/1.48  --splitting_grd                         true
% 7.03/1.48  --splitting_cvd                         false
% 7.03/1.48  --splitting_cvd_svl                     false
% 7.03/1.48  --splitting_nvd                         32
% 7.03/1.48  --sub_typing                            true
% 7.03/1.48  --prep_gs_sim                           true
% 7.03/1.48  --prep_unflatten                        true
% 7.03/1.48  --prep_res_sim                          true
% 7.03/1.48  --prep_upred                            true
% 7.03/1.48  --prep_sem_filter                       exhaustive
% 7.03/1.48  --prep_sem_filter_out                   false
% 7.03/1.48  --pred_elim                             true
% 7.03/1.48  --res_sim_input                         true
% 7.03/1.48  --eq_ax_congr_red                       true
% 7.03/1.48  --pure_diseq_elim                       true
% 7.03/1.48  --brand_transform                       false
% 7.03/1.48  --non_eq_to_eq                          false
% 7.03/1.48  --prep_def_merge                        true
% 7.03/1.48  --prep_def_merge_prop_impl              false
% 7.03/1.48  --prep_def_merge_mbd                    true
% 7.03/1.48  --prep_def_merge_tr_red                 false
% 7.03/1.48  --prep_def_merge_tr_cl                  false
% 7.03/1.48  --smt_preprocessing                     true
% 7.03/1.48  --smt_ac_axioms                         fast
% 7.03/1.48  --preprocessed_out                      false
% 7.03/1.48  --preprocessed_stats                    false
% 7.03/1.48  
% 7.03/1.48  ------ Abstraction refinement Options
% 7.03/1.48  
% 7.03/1.48  --abstr_ref                             []
% 7.03/1.48  --abstr_ref_prep                        false
% 7.03/1.48  --abstr_ref_until_sat                   false
% 7.03/1.48  --abstr_ref_sig_restrict                funpre
% 7.03/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.03/1.48  --abstr_ref_under                       []
% 7.03/1.48  
% 7.03/1.48  ------ SAT Options
% 7.03/1.48  
% 7.03/1.48  --sat_mode                              false
% 7.03/1.48  --sat_fm_restart_options                ""
% 7.03/1.48  --sat_gr_def                            false
% 7.03/1.48  --sat_epr_types                         true
% 7.03/1.48  --sat_non_cyclic_types                  false
% 7.03/1.48  --sat_finite_models                     false
% 7.03/1.48  --sat_fm_lemmas                         false
% 7.03/1.48  --sat_fm_prep                           false
% 7.03/1.48  --sat_fm_uc_incr                        true
% 7.03/1.48  --sat_out_model                         small
% 7.03/1.48  --sat_out_clauses                       false
% 7.03/1.48  
% 7.03/1.48  ------ QBF Options
% 7.03/1.48  
% 7.03/1.48  --qbf_mode                              false
% 7.03/1.48  --qbf_elim_univ                         false
% 7.03/1.48  --qbf_dom_inst                          none
% 7.03/1.48  --qbf_dom_pre_inst                      false
% 7.03/1.48  --qbf_sk_in                             false
% 7.03/1.48  --qbf_pred_elim                         true
% 7.03/1.48  --qbf_split                             512
% 7.03/1.48  
% 7.03/1.48  ------ BMC1 Options
% 7.03/1.48  
% 7.03/1.48  --bmc1_incremental                      false
% 7.03/1.48  --bmc1_axioms                           reachable_all
% 7.03/1.48  --bmc1_min_bound                        0
% 7.03/1.48  --bmc1_max_bound                        -1
% 7.03/1.48  --bmc1_max_bound_default                -1
% 7.03/1.48  --bmc1_symbol_reachability              true
% 7.03/1.48  --bmc1_property_lemmas                  false
% 7.03/1.48  --bmc1_k_induction                      false
% 7.03/1.48  --bmc1_non_equiv_states                 false
% 7.03/1.48  --bmc1_deadlock                         false
% 7.03/1.48  --bmc1_ucm                              false
% 7.03/1.48  --bmc1_add_unsat_core                   none
% 7.03/1.48  --bmc1_unsat_core_children              false
% 7.03/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.03/1.48  --bmc1_out_stat                         full
% 7.03/1.48  --bmc1_ground_init                      false
% 7.03/1.48  --bmc1_pre_inst_next_state              false
% 7.03/1.48  --bmc1_pre_inst_state                   false
% 7.03/1.48  --bmc1_pre_inst_reach_state             false
% 7.03/1.48  --bmc1_out_unsat_core                   false
% 7.03/1.48  --bmc1_aig_witness_out                  false
% 7.03/1.48  --bmc1_verbose                          false
% 7.03/1.48  --bmc1_dump_clauses_tptp                false
% 7.03/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.03/1.48  --bmc1_dump_file                        -
% 7.03/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.03/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.03/1.48  --bmc1_ucm_extend_mode                  1
% 7.03/1.48  --bmc1_ucm_init_mode                    2
% 7.03/1.48  --bmc1_ucm_cone_mode                    none
% 7.03/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.03/1.48  --bmc1_ucm_relax_model                  4
% 7.03/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.03/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.03/1.48  --bmc1_ucm_layered_model                none
% 7.03/1.48  --bmc1_ucm_max_lemma_size               10
% 7.03/1.48  
% 7.03/1.48  ------ AIG Options
% 7.03/1.48  
% 7.03/1.48  --aig_mode                              false
% 7.03/1.48  
% 7.03/1.48  ------ Instantiation Options
% 7.03/1.48  
% 7.03/1.48  --instantiation_flag                    true
% 7.03/1.48  --inst_sos_flag                         false
% 7.03/1.48  --inst_sos_phase                        true
% 7.03/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.03/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.03/1.48  --inst_lit_sel_side                     num_symb
% 7.03/1.48  --inst_solver_per_active                1400
% 7.03/1.48  --inst_solver_calls_frac                1.
% 7.03/1.48  --inst_passive_queue_type               priority_queues
% 7.03/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.03/1.48  --inst_passive_queues_freq              [25;2]
% 7.03/1.48  --inst_dismatching                      true
% 7.03/1.48  --inst_eager_unprocessed_to_passive     true
% 7.03/1.48  --inst_prop_sim_given                   true
% 7.03/1.48  --inst_prop_sim_new                     false
% 7.03/1.48  --inst_subs_new                         false
% 7.03/1.48  --inst_eq_res_simp                      false
% 7.03/1.48  --inst_subs_given                       false
% 7.03/1.48  --inst_orphan_elimination               true
% 7.03/1.48  --inst_learning_loop_flag               true
% 7.03/1.48  --inst_learning_start                   3000
% 7.03/1.48  --inst_learning_factor                  2
% 7.03/1.48  --inst_start_prop_sim_after_learn       3
% 7.03/1.48  --inst_sel_renew                        solver
% 7.03/1.48  --inst_lit_activity_flag                true
% 7.03/1.48  --inst_restr_to_given                   false
% 7.03/1.48  --inst_activity_threshold               500
% 7.03/1.48  --inst_out_proof                        true
% 7.03/1.48  
% 7.03/1.48  ------ Resolution Options
% 7.03/1.48  
% 7.03/1.48  --resolution_flag                       true
% 7.03/1.48  --res_lit_sel                           adaptive
% 7.03/1.48  --res_lit_sel_side                      none
% 7.03/1.48  --res_ordering                          kbo
% 7.03/1.48  --res_to_prop_solver                    active
% 7.03/1.48  --res_prop_simpl_new                    false
% 7.03/1.48  --res_prop_simpl_given                  true
% 7.03/1.48  --res_passive_queue_type                priority_queues
% 7.03/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.03/1.48  --res_passive_queues_freq               [15;5]
% 7.03/1.48  --res_forward_subs                      full
% 7.03/1.48  --res_backward_subs                     full
% 7.03/1.48  --res_forward_subs_resolution           true
% 7.03/1.48  --res_backward_subs_resolution          true
% 7.03/1.48  --res_orphan_elimination                true
% 7.03/1.48  --res_time_limit                        2.
% 7.03/1.48  --res_out_proof                         true
% 7.03/1.48  
% 7.03/1.48  ------ Superposition Options
% 7.03/1.48  
% 7.03/1.48  --superposition_flag                    true
% 7.03/1.48  --sup_passive_queue_type                priority_queues
% 7.03/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.03/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.03/1.48  --demod_completeness_check              fast
% 7.03/1.48  --demod_use_ground                      true
% 7.03/1.48  --sup_to_prop_solver                    passive
% 7.03/1.48  --sup_prop_simpl_new                    true
% 7.03/1.48  --sup_prop_simpl_given                  true
% 7.03/1.48  --sup_fun_splitting                     false
% 7.03/1.48  --sup_smt_interval                      50000
% 7.03/1.48  
% 7.03/1.48  ------ Superposition Simplification Setup
% 7.03/1.48  
% 7.03/1.48  --sup_indices_passive                   []
% 7.03/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.03/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.48  --sup_full_bw                           [BwDemod]
% 7.03/1.48  --sup_immed_triv                        [TrivRules]
% 7.03/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.03/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.48  --sup_immed_bw_main                     []
% 7.03/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.03/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.03/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.03/1.48  
% 7.03/1.48  ------ Combination Options
% 7.03/1.48  
% 7.03/1.48  --comb_res_mult                         3
% 7.03/1.48  --comb_sup_mult                         2
% 7.03/1.48  --comb_inst_mult                        10
% 7.03/1.48  
% 7.03/1.48  ------ Debug Options
% 7.03/1.48  
% 7.03/1.48  --dbg_backtrace                         false
% 7.03/1.48  --dbg_dump_prop_clauses                 false
% 7.03/1.48  --dbg_dump_prop_clauses_file            -
% 7.03/1.48  --dbg_out_stat                          false
% 7.03/1.48  ------ Parsing...
% 7.03/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.03/1.48  
% 7.03/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.03/1.48  
% 7.03/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.03/1.48  
% 7.03/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.03/1.48  ------ Proving...
% 7.03/1.48  ------ Problem Properties 
% 7.03/1.48  
% 7.03/1.48  
% 7.03/1.48  clauses                                 29
% 7.03/1.48  conjectures                             14
% 7.03/1.48  EPR                                     10
% 7.03/1.48  Horn                                    20
% 7.03/1.48  unary                                   14
% 7.03/1.48  binary                                  3
% 7.03/1.48  lits                                    127
% 7.03/1.48  lits eq                                 15
% 7.03/1.48  fd_pure                                 0
% 7.03/1.48  fd_pseudo                               0
% 7.03/1.48  fd_cond                                 0
% 7.03/1.48  fd_pseudo_cond                          1
% 7.03/1.48  AC symbols                              0
% 7.03/1.48  
% 7.03/1.48  ------ Schedule dynamic 5 is on 
% 7.03/1.48  
% 7.03/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.03/1.48  
% 7.03/1.48  
% 7.03/1.48  ------ 
% 7.03/1.48  Current options:
% 7.03/1.48  ------ 
% 7.03/1.48  
% 7.03/1.48  ------ Input Options
% 7.03/1.48  
% 7.03/1.48  --out_options                           all
% 7.03/1.48  --tptp_safe_out                         true
% 7.03/1.48  --problem_path                          ""
% 7.03/1.48  --include_path                          ""
% 7.03/1.48  --clausifier                            res/vclausify_rel
% 7.03/1.48  --clausifier_options                    --mode clausify
% 7.03/1.48  --stdin                                 false
% 7.03/1.48  --stats_out                             all
% 7.03/1.48  
% 7.03/1.48  ------ General Options
% 7.03/1.48  
% 7.03/1.48  --fof                                   false
% 7.03/1.48  --time_out_real                         305.
% 7.03/1.48  --time_out_virtual                      -1.
% 7.03/1.48  --symbol_type_check                     false
% 7.03/1.48  --clausify_out                          false
% 7.03/1.48  --sig_cnt_out                           false
% 7.03/1.48  --trig_cnt_out                          false
% 7.03/1.48  --trig_cnt_out_tolerance                1.
% 7.03/1.48  --trig_cnt_out_sk_spl                   false
% 7.03/1.48  --abstr_cl_out                          false
% 7.03/1.48  
% 7.03/1.48  ------ Global Options
% 7.03/1.48  
% 7.03/1.48  --schedule                              default
% 7.03/1.48  --add_important_lit                     false
% 7.03/1.48  --prop_solver_per_cl                    1000
% 7.03/1.48  --min_unsat_core                        false
% 7.03/1.48  --soft_assumptions                      false
% 7.03/1.48  --soft_lemma_size                       3
% 7.03/1.48  --prop_impl_unit_size                   0
% 7.03/1.48  --prop_impl_unit                        []
% 7.03/1.48  --share_sel_clauses                     true
% 7.03/1.48  --reset_solvers                         false
% 7.03/1.48  --bc_imp_inh                            [conj_cone]
% 7.03/1.48  --conj_cone_tolerance                   3.
% 7.03/1.48  --extra_neg_conj                        none
% 7.03/1.48  --large_theory_mode                     true
% 7.03/1.48  --prolific_symb_bound                   200
% 7.03/1.48  --lt_threshold                          2000
% 7.03/1.48  --clause_weak_htbl                      true
% 7.03/1.48  --gc_record_bc_elim                     false
% 7.03/1.48  
% 7.03/1.48  ------ Preprocessing Options
% 7.03/1.48  
% 7.03/1.48  --preprocessing_flag                    true
% 7.03/1.48  --time_out_prep_mult                    0.1
% 7.03/1.48  --splitting_mode                        input
% 7.03/1.48  --splitting_grd                         true
% 7.03/1.48  --splitting_cvd                         false
% 7.03/1.48  --splitting_cvd_svl                     false
% 7.03/1.48  --splitting_nvd                         32
% 7.03/1.48  --sub_typing                            true
% 7.03/1.48  --prep_gs_sim                           true
% 7.03/1.48  --prep_unflatten                        true
% 7.03/1.48  --prep_res_sim                          true
% 7.03/1.48  --prep_upred                            true
% 7.03/1.48  --prep_sem_filter                       exhaustive
% 7.03/1.48  --prep_sem_filter_out                   false
% 7.03/1.48  --pred_elim                             true
% 7.03/1.48  --res_sim_input                         true
% 7.03/1.48  --eq_ax_congr_red                       true
% 7.03/1.48  --pure_diseq_elim                       true
% 7.03/1.48  --brand_transform                       false
% 7.03/1.48  --non_eq_to_eq                          false
% 7.03/1.48  --prep_def_merge                        true
% 7.03/1.48  --prep_def_merge_prop_impl              false
% 7.03/1.48  --prep_def_merge_mbd                    true
% 7.03/1.48  --prep_def_merge_tr_red                 false
% 7.03/1.48  --prep_def_merge_tr_cl                  false
% 7.03/1.48  --smt_preprocessing                     true
% 7.03/1.48  --smt_ac_axioms                         fast
% 7.03/1.48  --preprocessed_out                      false
% 7.03/1.48  --preprocessed_stats                    false
% 7.03/1.48  
% 7.03/1.48  ------ Abstraction refinement Options
% 7.03/1.48  
% 7.03/1.48  --abstr_ref                             []
% 7.03/1.48  --abstr_ref_prep                        false
% 7.03/1.48  --abstr_ref_until_sat                   false
% 7.03/1.48  --abstr_ref_sig_restrict                funpre
% 7.03/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.03/1.48  --abstr_ref_under                       []
% 7.03/1.48  
% 7.03/1.48  ------ SAT Options
% 7.03/1.48  
% 7.03/1.48  --sat_mode                              false
% 7.03/1.48  --sat_fm_restart_options                ""
% 7.03/1.48  --sat_gr_def                            false
% 7.03/1.48  --sat_epr_types                         true
% 7.03/1.48  --sat_non_cyclic_types                  false
% 7.03/1.48  --sat_finite_models                     false
% 7.03/1.48  --sat_fm_lemmas                         false
% 7.03/1.48  --sat_fm_prep                           false
% 7.03/1.48  --sat_fm_uc_incr                        true
% 7.03/1.48  --sat_out_model                         small
% 7.03/1.48  --sat_out_clauses                       false
% 7.03/1.48  
% 7.03/1.48  ------ QBF Options
% 7.03/1.48  
% 7.03/1.48  --qbf_mode                              false
% 7.03/1.48  --qbf_elim_univ                         false
% 7.03/1.48  --qbf_dom_inst                          none
% 7.03/1.48  --qbf_dom_pre_inst                      false
% 7.03/1.48  --qbf_sk_in                             false
% 7.03/1.48  --qbf_pred_elim                         true
% 7.03/1.48  --qbf_split                             512
% 7.03/1.48  
% 7.03/1.48  ------ BMC1 Options
% 7.03/1.48  
% 7.03/1.48  --bmc1_incremental                      false
% 7.03/1.48  --bmc1_axioms                           reachable_all
% 7.03/1.48  --bmc1_min_bound                        0
% 7.03/1.48  --bmc1_max_bound                        -1
% 7.03/1.48  --bmc1_max_bound_default                -1
% 7.03/1.48  --bmc1_symbol_reachability              true
% 7.03/1.48  --bmc1_property_lemmas                  false
% 7.03/1.48  --bmc1_k_induction                      false
% 7.03/1.48  --bmc1_non_equiv_states                 false
% 7.03/1.48  --bmc1_deadlock                         false
% 7.03/1.48  --bmc1_ucm                              false
% 7.03/1.48  --bmc1_add_unsat_core                   none
% 7.03/1.48  --bmc1_unsat_core_children              false
% 7.03/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.03/1.48  --bmc1_out_stat                         full
% 7.03/1.48  --bmc1_ground_init                      false
% 7.03/1.48  --bmc1_pre_inst_next_state              false
% 7.03/1.48  --bmc1_pre_inst_state                   false
% 7.03/1.48  --bmc1_pre_inst_reach_state             false
% 7.03/1.48  --bmc1_out_unsat_core                   false
% 7.03/1.48  --bmc1_aig_witness_out                  false
% 7.03/1.48  --bmc1_verbose                          false
% 7.03/1.48  --bmc1_dump_clauses_tptp                false
% 7.03/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.03/1.48  --bmc1_dump_file                        -
% 7.03/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.03/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.03/1.48  --bmc1_ucm_extend_mode                  1
% 7.03/1.48  --bmc1_ucm_init_mode                    2
% 7.03/1.48  --bmc1_ucm_cone_mode                    none
% 7.03/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.03/1.48  --bmc1_ucm_relax_model                  4
% 7.03/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.03/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.03/1.48  --bmc1_ucm_layered_model                none
% 7.03/1.48  --bmc1_ucm_max_lemma_size               10
% 7.03/1.48  
% 7.03/1.48  ------ AIG Options
% 7.03/1.48  
% 7.03/1.48  --aig_mode                              false
% 7.03/1.48  
% 7.03/1.48  ------ Instantiation Options
% 7.03/1.48  
% 7.03/1.48  --instantiation_flag                    true
% 7.03/1.48  --inst_sos_flag                         false
% 7.03/1.48  --inst_sos_phase                        true
% 7.03/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.03/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.03/1.48  --inst_lit_sel_side                     none
% 7.03/1.48  --inst_solver_per_active                1400
% 7.03/1.48  --inst_solver_calls_frac                1.
% 7.03/1.48  --inst_passive_queue_type               priority_queues
% 7.03/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.03/1.48  --inst_passive_queues_freq              [25;2]
% 7.03/1.48  --inst_dismatching                      true
% 7.03/1.48  --inst_eager_unprocessed_to_passive     true
% 7.03/1.48  --inst_prop_sim_given                   true
% 7.03/1.48  --inst_prop_sim_new                     false
% 7.03/1.48  --inst_subs_new                         false
% 7.03/1.48  --inst_eq_res_simp                      false
% 7.03/1.48  --inst_subs_given                       false
% 7.03/1.48  --inst_orphan_elimination               true
% 7.03/1.48  --inst_learning_loop_flag               true
% 7.03/1.48  --inst_learning_start                   3000
% 7.03/1.48  --inst_learning_factor                  2
% 7.03/1.48  --inst_start_prop_sim_after_learn       3
% 7.03/1.48  --inst_sel_renew                        solver
% 7.03/1.48  --inst_lit_activity_flag                true
% 7.03/1.48  --inst_restr_to_given                   false
% 7.03/1.48  --inst_activity_threshold               500
% 7.03/1.48  --inst_out_proof                        true
% 7.03/1.48  
% 7.03/1.48  ------ Resolution Options
% 7.03/1.48  
% 7.03/1.48  --resolution_flag                       false
% 7.03/1.48  --res_lit_sel                           adaptive
% 7.03/1.48  --res_lit_sel_side                      none
% 7.03/1.48  --res_ordering                          kbo
% 7.03/1.48  --res_to_prop_solver                    active
% 7.03/1.48  --res_prop_simpl_new                    false
% 7.03/1.48  --res_prop_simpl_given                  true
% 7.03/1.48  --res_passive_queue_type                priority_queues
% 7.03/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.03/1.48  --res_passive_queues_freq               [15;5]
% 7.03/1.48  --res_forward_subs                      full
% 7.03/1.48  --res_backward_subs                     full
% 7.03/1.48  --res_forward_subs_resolution           true
% 7.03/1.48  --res_backward_subs_resolution          true
% 7.03/1.48  --res_orphan_elimination                true
% 7.03/1.48  --res_time_limit                        2.
% 7.03/1.48  --res_out_proof                         true
% 7.03/1.48  
% 7.03/1.48  ------ Superposition Options
% 7.03/1.48  
% 7.03/1.48  --superposition_flag                    true
% 7.03/1.48  --sup_passive_queue_type                priority_queues
% 7.03/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.03/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.03/1.48  --demod_completeness_check              fast
% 7.03/1.48  --demod_use_ground                      true
% 7.03/1.48  --sup_to_prop_solver                    passive
% 7.03/1.48  --sup_prop_simpl_new                    true
% 7.03/1.48  --sup_prop_simpl_given                  true
% 7.03/1.48  --sup_fun_splitting                     false
% 7.03/1.48  --sup_smt_interval                      50000
% 7.03/1.48  
% 7.03/1.48  ------ Superposition Simplification Setup
% 7.03/1.48  
% 7.03/1.48  --sup_indices_passive                   []
% 7.03/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.03/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.03/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.48  --sup_full_bw                           [BwDemod]
% 7.03/1.48  --sup_immed_triv                        [TrivRules]
% 7.03/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.03/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.48  --sup_immed_bw_main                     []
% 7.03/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.03/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.03/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.03/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.03/1.48  
% 7.03/1.48  ------ Combination Options
% 7.03/1.48  
% 7.03/1.48  --comb_res_mult                         3
% 7.03/1.48  --comb_sup_mult                         2
% 7.03/1.48  --comb_inst_mult                        10
% 7.03/1.48  
% 7.03/1.48  ------ Debug Options
% 7.03/1.48  
% 7.03/1.48  --dbg_backtrace                         false
% 7.03/1.48  --dbg_dump_prop_clauses                 false
% 7.03/1.48  --dbg_dump_prop_clauses_file            -
% 7.03/1.48  --dbg_out_stat                          false
% 7.03/1.48  
% 7.03/1.48  
% 7.03/1.48  
% 7.03/1.48  
% 7.03/1.48  ------ Proving...
% 7.03/1.48  
% 7.03/1.48  
% 7.03/1.48  % SZS status Theorem for theBenchmark.p
% 7.03/1.48  
% 7.03/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.03/1.48  
% 7.03/1.48  fof(f15,conjecture,(
% 7.03/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f16,negated_conjecture,(
% 7.03/1.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.03/1.48    inference(negated_conjecture,[],[f15])).
% 7.03/1.48  
% 7.03/1.48  fof(f38,plain,(
% 7.03/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.03/1.48    inference(ennf_transformation,[],[f16])).
% 7.03/1.48  
% 7.03/1.48  fof(f39,plain,(
% 7.03/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.03/1.48    inference(flattening,[],[f38])).
% 7.03/1.48  
% 7.03/1.48  fof(f49,plain,(
% 7.03/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.03/1.48    introduced(choice_axiom,[])).
% 7.03/1.48  
% 7.03/1.48  fof(f48,plain,(
% 7.03/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.03/1.48    introduced(choice_axiom,[])).
% 7.03/1.48  
% 7.03/1.48  fof(f47,plain,(
% 7.03/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.03/1.48    introduced(choice_axiom,[])).
% 7.03/1.48  
% 7.03/1.48  fof(f46,plain,(
% 7.03/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.03/1.48    introduced(choice_axiom,[])).
% 7.03/1.48  
% 7.03/1.48  fof(f45,plain,(
% 7.03/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.03/1.48    introduced(choice_axiom,[])).
% 7.03/1.48  
% 7.03/1.48  fof(f44,plain,(
% 7.03/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.03/1.48    introduced(choice_axiom,[])).
% 7.03/1.48  
% 7.03/1.48  fof(f50,plain,(
% 7.03/1.48    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.03/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f39,f49,f48,f47,f46,f45,f44])).
% 7.03/1.48  
% 7.03/1.48  fof(f77,plain,(
% 7.03/1.48    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f2,axiom,(
% 7.03/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f18,plain,(
% 7.03/1.48    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.03/1.48    inference(ennf_transformation,[],[f2])).
% 7.03/1.48  
% 7.03/1.48  fof(f52,plain,(
% 7.03/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.03/1.48    inference(cnf_transformation,[],[f18])).
% 7.03/1.48  
% 7.03/1.48  fof(f84,plain,(
% 7.03/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f12,axiom,(
% 7.03/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f32,plain,(
% 7.03/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.03/1.48    inference(ennf_transformation,[],[f12])).
% 7.03/1.48  
% 7.03/1.48  fof(f33,plain,(
% 7.03/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.03/1.48    inference(flattening,[],[f32])).
% 7.03/1.48  
% 7.03/1.48  fof(f65,plain,(
% 7.03/1.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f33])).
% 7.03/1.48  
% 7.03/1.48  fof(f82,plain,(
% 7.03/1.48    v1_funct_1(sK5)),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f81,plain,(
% 7.03/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f79,plain,(
% 7.03/1.48    v1_funct_1(sK4)),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f13,axiom,(
% 7.03/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f34,plain,(
% 7.03/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.03/1.48    inference(ennf_transformation,[],[f13])).
% 7.03/1.48  
% 7.03/1.48  fof(f35,plain,(
% 7.03/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.03/1.48    inference(flattening,[],[f34])).
% 7.03/1.48  
% 7.03/1.48  fof(f42,plain,(
% 7.03/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.03/1.48    inference(nnf_transformation,[],[f35])).
% 7.03/1.48  
% 7.03/1.48  fof(f43,plain,(
% 7.03/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.03/1.48    inference(flattening,[],[f42])).
% 7.03/1.48  
% 7.03/1.48  fof(f67,plain,(
% 7.03/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f43])).
% 7.03/1.48  
% 7.03/1.48  fof(f89,plain,(
% 7.03/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.03/1.48    inference(equality_resolution,[],[f67])).
% 7.03/1.48  
% 7.03/1.48  fof(f14,axiom,(
% 7.03/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f36,plain,(
% 7.03/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.03/1.48    inference(ennf_transformation,[],[f14])).
% 7.03/1.48  
% 7.03/1.48  fof(f37,plain,(
% 7.03/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.03/1.48    inference(flattening,[],[f36])).
% 7.03/1.48  
% 7.03/1.48  fof(f69,plain,(
% 7.03/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f37])).
% 7.03/1.48  
% 7.03/1.48  fof(f70,plain,(
% 7.03/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f37])).
% 7.03/1.48  
% 7.03/1.48  fof(f71,plain,(
% 7.03/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f37])).
% 7.03/1.48  
% 7.03/1.48  fof(f3,axiom,(
% 7.03/1.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f19,plain,(
% 7.03/1.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.03/1.48    inference(ennf_transformation,[],[f3])).
% 7.03/1.48  
% 7.03/1.48  fof(f53,plain,(
% 7.03/1.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f19])).
% 7.03/1.48  
% 7.03/1.48  fof(f73,plain,(
% 7.03/1.48    ~v1_xboole_0(sK1)),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f74,plain,(
% 7.03/1.48    ~v1_xboole_0(sK2)),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f80,plain,(
% 7.03/1.48    v1_funct_2(sK4,sK2,sK1)),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f76,plain,(
% 7.03/1.48    ~v1_xboole_0(sK3)),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f83,plain,(
% 7.03/1.48    v1_funct_2(sK5,sK3,sK1)),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f10,axiom,(
% 7.03/1.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f28,plain,(
% 7.03/1.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.03/1.48    inference(ennf_transformation,[],[f10])).
% 7.03/1.48  
% 7.03/1.48  fof(f29,plain,(
% 7.03/1.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 7.03/1.48    inference(flattening,[],[f28])).
% 7.03/1.48  
% 7.03/1.48  fof(f62,plain,(
% 7.03/1.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f29])).
% 7.03/1.48  
% 7.03/1.48  fof(f9,axiom,(
% 7.03/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f17,plain,(
% 7.03/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.03/1.48    inference(pure_predicate_removal,[],[f9])).
% 7.03/1.48  
% 7.03/1.48  fof(f27,plain,(
% 7.03/1.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.03/1.48    inference(ennf_transformation,[],[f17])).
% 7.03/1.48  
% 7.03/1.48  fof(f60,plain,(
% 7.03/1.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.03/1.48    inference(cnf_transformation,[],[f27])).
% 7.03/1.48  
% 7.03/1.48  fof(f11,axiom,(
% 7.03/1.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f30,plain,(
% 7.03/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.03/1.48    inference(ennf_transformation,[],[f11])).
% 7.03/1.48  
% 7.03/1.48  fof(f31,plain,(
% 7.03/1.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.03/1.48    inference(flattening,[],[f30])).
% 7.03/1.48  
% 7.03/1.48  fof(f41,plain,(
% 7.03/1.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.03/1.48    inference(nnf_transformation,[],[f31])).
% 7.03/1.48  
% 7.03/1.48  fof(f63,plain,(
% 7.03/1.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f41])).
% 7.03/1.48  
% 7.03/1.48  fof(f8,axiom,(
% 7.03/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f26,plain,(
% 7.03/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.03/1.48    inference(ennf_transformation,[],[f8])).
% 7.03/1.48  
% 7.03/1.48  fof(f59,plain,(
% 7.03/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.03/1.48    inference(cnf_transformation,[],[f26])).
% 7.03/1.48  
% 7.03/1.48  fof(f1,axiom,(
% 7.03/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f51,plain,(
% 7.03/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f1])).
% 7.03/1.48  
% 7.03/1.48  fof(f5,axiom,(
% 7.03/1.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f21,plain,(
% 7.03/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.03/1.48    inference(ennf_transformation,[],[f5])).
% 7.03/1.48  
% 7.03/1.48  fof(f55,plain,(
% 7.03/1.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f21])).
% 7.03/1.48  
% 7.03/1.48  fof(f78,plain,(
% 7.03/1.48    r1_subset_1(sK2,sK3)),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f4,axiom,(
% 7.03/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f20,plain,(
% 7.03/1.48    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.03/1.48    inference(ennf_transformation,[],[f4])).
% 7.03/1.48  
% 7.03/1.48  fof(f54,plain,(
% 7.03/1.48    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f20])).
% 7.03/1.48  
% 7.03/1.48  fof(f6,axiom,(
% 7.03/1.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f22,plain,(
% 7.03/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.03/1.48    inference(ennf_transformation,[],[f6])).
% 7.03/1.48  
% 7.03/1.48  fof(f23,plain,(
% 7.03/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.03/1.48    inference(flattening,[],[f22])).
% 7.03/1.48  
% 7.03/1.48  fof(f40,plain,(
% 7.03/1.48    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.03/1.48    inference(nnf_transformation,[],[f23])).
% 7.03/1.48  
% 7.03/1.48  fof(f56,plain,(
% 7.03/1.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f40])).
% 7.03/1.48  
% 7.03/1.48  fof(f75,plain,(
% 7.03/1.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  fof(f7,axiom,(
% 7.03/1.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) => r1_subset_1(X1,X0)))),
% 7.03/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.03/1.48  
% 7.03/1.48  fof(f24,plain,(
% 7.03/1.48    ! [X0,X1] : ((r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.03/1.48    inference(ennf_transformation,[],[f7])).
% 7.03/1.48  
% 7.03/1.48  fof(f25,plain,(
% 7.03/1.48    ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.03/1.48    inference(flattening,[],[f24])).
% 7.03/1.48  
% 7.03/1.48  fof(f58,plain,(
% 7.03/1.48    ( ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f25])).
% 7.03/1.48  
% 7.03/1.48  fof(f66,plain,(
% 7.03/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.03/1.48    inference(cnf_transformation,[],[f43])).
% 7.03/1.48  
% 7.03/1.48  fof(f90,plain,(
% 7.03/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.03/1.48    inference(equality_resolution,[],[f66])).
% 7.03/1.48  
% 7.03/1.48  fof(f85,plain,(
% 7.03/1.48    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.03/1.48    inference(cnf_transformation,[],[f50])).
% 7.03/1.48  
% 7.03/1.48  cnf(c_29,negated_conjecture,
% 7.03/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.03/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_757,negated_conjecture,
% 7.03/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_29]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1291,plain,
% 7.03/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1,plain,
% 7.03/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.03/1.48      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.03/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_775,plain,
% 7.03/1.48      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.03/1.48      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_1]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1274,plain,
% 7.03/1.48      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 7.03/1.48      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_775]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1927,plain,
% 7.03/1.48      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1291,c_1274]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_22,negated_conjecture,
% 7.03/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.03/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_764,negated_conjecture,
% 7.03/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_22]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1284,plain,
% 7.03/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_14,plain,
% 7.03/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.03/1.48      inference(cnf_transformation,[],[f65]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_770,plain,
% 7.03/1.48      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.03/1.48      | ~ v1_funct_1(X0_53)
% 7.03/1.48      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_14]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1279,plain,
% 7.03/1.48      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 7.03/1.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.03/1.48      | v1_funct_1(X2_53) != iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_770]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2306,plain,
% 7.03/1.48      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 7.03/1.48      | v1_funct_1(sK5) != iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1284,c_1279]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_24,negated_conjecture,
% 7.03/1.48      ( v1_funct_1(sK5) ),
% 7.03/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1703,plain,
% 7.03/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.03/1.48      | ~ v1_funct_1(sK5)
% 7.03/1.48      | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
% 7.03/1.48      inference(instantiation,[status(thm)],[c_770]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1879,plain,
% 7.03/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.03/1.48      | ~ v1_funct_1(sK5)
% 7.03/1.48      | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.03/1.48      inference(instantiation,[status(thm)],[c_1703]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2511,plain,
% 7.03/1.48      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_2306,c_24,c_22,c_1879]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_25,negated_conjecture,
% 7.03/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.03/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_761,negated_conjecture,
% 7.03/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_25]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1287,plain,
% 7.03/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2307,plain,
% 7.03/1.48      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 7.03/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1287,c_1279]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_27,negated_conjecture,
% 7.03/1.48      ( v1_funct_1(sK4) ),
% 7.03/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1708,plain,
% 7.03/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.03/1.48      | ~ v1_funct_1(sK4)
% 7.03/1.48      | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
% 7.03/1.48      inference(instantiation,[status(thm)],[c_770]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1884,plain,
% 7.03/1.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.03/1.48      | ~ v1_funct_1(sK4)
% 7.03/1.48      | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.03/1.48      inference(instantiation,[status(thm)],[c_1708]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2517,plain,
% 7.03/1.48      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_2307,c_27,c_25,c_1884]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_16,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.03/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.03/1.48      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.03/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.03/1.48      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | ~ v1_funct_1(X3)
% 7.03/1.48      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.03/1.48      | v1_xboole_0(X5)
% 7.03/1.48      | v1_xboole_0(X2)
% 7.03/1.48      | v1_xboole_0(X4)
% 7.03/1.48      | v1_xboole_0(X1)
% 7.03/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.03/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.03/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_20,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.03/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.03/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | ~ v1_funct_1(X3)
% 7.03/1.48      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.03/1.48      | v1_xboole_0(X5)
% 7.03/1.48      | v1_xboole_0(X2)
% 7.03/1.48      | v1_xboole_0(X4)
% 7.03/1.48      | v1_xboole_0(X1) ),
% 7.03/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_19,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.03/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.03/1.48      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.03/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | ~ v1_funct_1(X3)
% 7.03/1.48      | v1_xboole_0(X5)
% 7.03/1.48      | v1_xboole_0(X2)
% 7.03/1.48      | v1_xboole_0(X4)
% 7.03/1.48      | v1_xboole_0(X1) ),
% 7.03/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_18,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.03/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.03/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.03/1.48      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | ~ v1_funct_1(X3)
% 7.03/1.48      | v1_xboole_0(X5)
% 7.03/1.48      | v1_xboole_0(X2)
% 7.03/1.48      | v1_xboole_0(X4)
% 7.03/1.48      | v1_xboole_0(X1) ),
% 7.03/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_191,plain,
% 7.03/1.48      ( ~ v1_funct_1(X3)
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.03/1.48      | ~ v1_funct_2(X0,X1,X2)
% 7.03/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.03/1.48      | v1_xboole_0(X5)
% 7.03/1.48      | v1_xboole_0(X2)
% 7.03/1.48      | v1_xboole_0(X4)
% 7.03/1.48      | v1_xboole_0(X1)
% 7.03/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.03/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_16,c_20,c_19,c_18]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_192,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.03/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.03/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | ~ v1_funct_1(X3)
% 7.03/1.48      | v1_xboole_0(X1)
% 7.03/1.48      | v1_xboole_0(X2)
% 7.03/1.48      | v1_xboole_0(X4)
% 7.03/1.48      | v1_xboole_0(X5)
% 7.03/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.03/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.03/1.48      inference(renaming,[status(thm)],[c_191]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_750,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.03/1.48      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.03/1.48      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.03/1.48      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.03/1.48      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.03/1.48      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.03/1.48      | ~ v1_funct_1(X0_53)
% 7.03/1.48      | ~ v1_funct_1(X3_53)
% 7.03/1.48      | v1_xboole_0(X2_53)
% 7.03/1.48      | v1_xboole_0(X1_53)
% 7.03/1.48      | v1_xboole_0(X4_53)
% 7.03/1.48      | v1_xboole_0(X5_53)
% 7.03/1.48      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.03/1.48      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_192]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1298,plain,
% 7.03/1.48      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.03/1.48      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 7.03/1.48      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.03/1.48      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.03/1.48      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.03/1.48      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.03/1.48      | v1_funct_1(X2_53) != iProver_top
% 7.03/1.48      | v1_funct_1(X5_53) != iProver_top
% 7.03/1.48      | v1_xboole_0(X3_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X4_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2,plain,
% 7.03/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.03/1.48      | ~ v1_xboole_0(X1)
% 7.03/1.48      | v1_xboole_0(X0) ),
% 7.03/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_774,plain,
% 7.03/1.48      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 7.03/1.48      | ~ v1_xboole_0(X1_53)
% 7.03/1.48      | v1_xboole_0(X0_53) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1275,plain,
% 7.03/1.48      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) != iProver_top
% 7.03/1.48      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_774]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1507,plain,
% 7.03/1.48      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 7.03/1.48      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X4_53) = X5_53
% 7.03/1.48      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.03/1.48      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.03/1.48      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.03/1.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.03/1.48      | v1_funct_1(X5_53) != iProver_top
% 7.03/1.48      | v1_funct_1(X2_53) != iProver_top
% 7.03/1.48      | v1_xboole_0(X0_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X4_53) = iProver_top ),
% 7.03/1.48      inference(forward_subsumption_resolution,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_1298,c_1275]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_6452,plain,
% 7.03/1.48      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.03/1.48      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.03/1.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.03/1.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.03/1.48      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.03/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.03/1.48      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.48      | v1_funct_1(X1_53) != iProver_top
% 7.03/1.48      | v1_funct_1(sK4) != iProver_top
% 7.03/1.48      | v1_xboole_0(X0_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(sK1) = iProver_top
% 7.03/1.48      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_2517,c_1507]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_33,negated_conjecture,
% 7.03/1.48      ( ~ v1_xboole_0(sK1) ),
% 7.03/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_36,plain,
% 7.03/1.48      ( v1_xboole_0(sK1) != iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_32,negated_conjecture,
% 7.03/1.48      ( ~ v1_xboole_0(sK2) ),
% 7.03/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_37,plain,
% 7.03/1.48      ( v1_xboole_0(sK2) != iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_42,plain,
% 7.03/1.48      ( v1_funct_1(sK4) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_26,negated_conjecture,
% 7.03/1.48      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.03/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_43,plain,
% 7.03/1.48      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_44,plain,
% 7.03/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_17951,plain,
% 7.03/1.48      ( v1_funct_1(X1_53) != iProver_top
% 7.03/1.48      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.03/1.48      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.03/1.48      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.03/1.48      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.03/1.48      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_6452,c_36,c_37,c_42,c_43,c_44]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_17952,plain,
% 7.03/1.48      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,sK2,X0_53)) != k7_relat_1(sK4,k9_subset_1(X2_53,sK2,X0_53))
% 7.03/1.48      | k2_partfun1(k4_subset_1(X2_53,sK2,X0_53),sK1,k1_tmap_1(X2_53,sK1,sK2,X0_53,sK4,X1_53),X0_53) = X1_53
% 7.03/1.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.03/1.48      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.03/1.48      | m1_subset_1(sK2,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.48      | v1_funct_1(X1_53) != iProver_top
% 7.03/1.48      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.48      inference(renaming,[status(thm)],[c_17951]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_17965,plain,
% 7.03/1.48      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.03/1.48      | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
% 7.03/1.48      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.03/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.03/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | v1_funct_1(sK5) != iProver_top
% 7.03/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_2511,c_17952]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_30,negated_conjecture,
% 7.03/1.48      ( ~ v1_xboole_0(sK3) ),
% 7.03/1.48      inference(cnf_transformation,[],[f76]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_39,plain,
% 7.03/1.48      ( v1_xboole_0(sK3) != iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_45,plain,
% 7.03/1.48      ( v1_funct_1(sK5) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_23,negated_conjecture,
% 7.03/1.48      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.03/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_46,plain,
% 7.03/1.48      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_47,plain,
% 7.03/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_18343,plain,
% 7.03/1.48      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.03/1.48      | k7_relat_1(sK4,k9_subset_1(X0_53,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0_53,sK2,sK3))
% 7.03/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_17965,c_39,c_45,c_46,c_47]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_18353,plain,
% 7.03/1.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.03/1.48      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.03/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.48      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1927,c_18343]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_10,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.03/1.48      | v1_partfun1(X0,X1)
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | v1_xboole_0(X2) ),
% 7.03/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_9,plain,
% 7.03/1.48      ( v4_relat_1(X0,X1)
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.03/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_13,plain,
% 7.03/1.48      ( ~ v1_partfun1(X0,X1)
% 7.03/1.48      | ~ v4_relat_1(X0,X1)
% 7.03/1.48      | ~ v1_relat_1(X0)
% 7.03/1.48      | k1_relat_1(X0) = X1 ),
% 7.03/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_360,plain,
% 7.03/1.48      ( ~ v1_partfun1(X0,X1)
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ v1_relat_1(X0)
% 7.03/1.48      | k1_relat_1(X0) = X1 ),
% 7.03/1.48      inference(resolution,[status(thm)],[c_9,c_13]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_8,plain,
% 7.03/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | v1_relat_1(X0) ),
% 7.03/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_364,plain,
% 7.03/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ v1_partfun1(X0,X1)
% 7.03/1.48      | k1_relat_1(X0) = X1 ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_360,c_13,c_9,c_8]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_365,plain,
% 7.03/1.48      ( ~ v1_partfun1(X0,X1)
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | k1_relat_1(X0) = X1 ),
% 7.03/1.48      inference(renaming,[status(thm)],[c_364]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_435,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | v1_xboole_0(X2)
% 7.03/1.48      | k1_relat_1(X0) = X1 ),
% 7.03/1.48      inference(resolution,[status(thm)],[c_10,c_365]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_439,plain,
% 7.03/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ v1_funct_2(X0,X1,X2)
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | v1_xboole_0(X2)
% 7.03/1.48      | k1_relat_1(X0) = X1 ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_435,c_13,c_10,c_9,c_8]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_440,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.03/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.48      | ~ v1_funct_1(X0)
% 7.03/1.48      | v1_xboole_0(X2)
% 7.03/1.48      | k1_relat_1(X0) = X1 ),
% 7.03/1.48      inference(renaming,[status(thm)],[c_439]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_749,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.03/1.48      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.03/1.48      | ~ v1_funct_1(X0_53)
% 7.03/1.48      | v1_xboole_0(X2_53)
% 7.03/1.48      | k1_relat_1(X0_53) = X1_53 ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_440]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1299,plain,
% 7.03/1.48      ( k1_relat_1(X0_53) = X1_53
% 7.03/1.48      | v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.03/1.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.03/1.48      | v1_funct_1(X0_53) != iProver_top
% 7.03/1.48      | v1_xboole_0(X2_53) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2634,plain,
% 7.03/1.48      ( k1_relat_1(sK5) = sK3
% 7.03/1.48      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.03/1.48      | v1_funct_1(sK5) != iProver_top
% 7.03/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1284,c_1299]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1693,plain,
% 7.03/1.48      ( ~ v1_funct_2(sK5,X0_53,X1_53)
% 7.03/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.03/1.48      | ~ v1_funct_1(sK5)
% 7.03/1.48      | v1_xboole_0(X1_53)
% 7.03/1.48      | k1_relat_1(sK5) = X0_53 ),
% 7.03/1.48      inference(instantiation,[status(thm)],[c_749]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1873,plain,
% 7.03/1.48      ( ~ v1_funct_2(sK5,sK3,sK1)
% 7.03/1.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.03/1.48      | ~ v1_funct_1(sK5)
% 7.03/1.48      | v1_xboole_0(sK1)
% 7.03/1.48      | k1_relat_1(sK5) = sK3 ),
% 7.03/1.48      inference(instantiation,[status(thm)],[c_1693]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_3135,plain,
% 7.03/1.48      ( k1_relat_1(sK5) = sK3 ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_2634,c_33,c_24,c_23,c_22,c_1873]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_0,plain,
% 7.03/1.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.03/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_776,plain,
% 7.03/1.48      ( k3_xboole_0(X0_53,X1_53) = k3_xboole_0(X1_53,X0_53) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_0]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_771,plain,
% 7.03/1.48      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.03/1.48      | v1_relat_1(X0_53) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_8]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1278,plain,
% 7.03/1.48      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.03/1.48      | v1_relat_1(X0_53) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_771]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2249,plain,
% 7.03/1.48      ( v1_relat_1(sK5) = iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1284,c_1278]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_4,plain,
% 7.03/1.48      ( ~ v1_relat_1(X0)
% 7.03/1.48      | k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) = k7_relat_1(X0,X1) ),
% 7.03/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_773,plain,
% 7.03/1.48      ( ~ v1_relat_1(X0_53)
% 7.03/1.48      | k7_relat_1(X0_53,k3_xboole_0(k1_relat_1(X0_53),X1_53)) = k7_relat_1(X0_53,X1_53) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1276,plain,
% 7.03/1.48      ( k7_relat_1(X0_53,k3_xboole_0(k1_relat_1(X0_53),X1_53)) = k7_relat_1(X0_53,X1_53)
% 7.03/1.48      | v1_relat_1(X0_53) != iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2372,plain,
% 7.03/1.48      ( k7_relat_1(sK5,k3_xboole_0(k1_relat_1(sK5),X0_53)) = k7_relat_1(sK5,X0_53) ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_2249,c_1276]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2655,plain,
% 7.03/1.48      ( k7_relat_1(sK5,k3_xboole_0(X0_53,k1_relat_1(sK5))) = k7_relat_1(sK5,X0_53) ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_776,c_2372]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_3138,plain,
% 7.03/1.48      ( k7_relat_1(sK5,k3_xboole_0(X0_53,sK3)) = k7_relat_1(sK5,X0_53) ),
% 7.03/1.48      inference(demodulation,[status(thm)],[c_3135,c_2655]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2635,plain,
% 7.03/1.48      ( k1_relat_1(sK4) = sK2
% 7.03/1.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.03/1.48      | v1_funct_1(sK4) != iProver_top
% 7.03/1.48      | v1_xboole_0(sK1) = iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1287,c_1299]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1698,plain,
% 7.03/1.48      ( ~ v1_funct_2(sK4,X0_53,X1_53)
% 7.03/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 7.03/1.48      | ~ v1_funct_1(sK4)
% 7.03/1.48      | v1_xboole_0(X1_53)
% 7.03/1.48      | k1_relat_1(sK4) = X0_53 ),
% 7.03/1.48      inference(instantiation,[status(thm)],[c_749]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1876,plain,
% 7.03/1.48      ( ~ v1_funct_2(sK4,sK2,sK1)
% 7.03/1.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.03/1.48      | ~ v1_funct_1(sK4)
% 7.03/1.48      | v1_xboole_0(sK1)
% 7.03/1.48      | k1_relat_1(sK4) = sK2 ),
% 7.03/1.48      inference(instantiation,[status(thm)],[c_1698]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_3263,plain,
% 7.03/1.48      ( k1_relat_1(sK4) = sK2 ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_2635,c_33,c_27,c_26,c_25,c_1876]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2250,plain,
% 7.03/1.48      ( v1_relat_1(sK4) = iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1287,c_1278]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_2376,plain,
% 7.03/1.48      ( k7_relat_1(sK4,k3_xboole_0(k1_relat_1(sK4),X0_53)) = k7_relat_1(sK4,X0_53) ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_2250,c_1276]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_3267,plain,
% 7.03/1.48      ( k7_relat_1(sK4,k3_xboole_0(sK2,X0_53)) = k7_relat_1(sK4,X0_53) ),
% 7.03/1.48      inference(demodulation,[status(thm)],[c_3263,c_2376]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_28,negated_conjecture,
% 7.03/1.48      ( r1_subset_1(sK2,sK3) ),
% 7.03/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_758,negated_conjecture,
% 7.03/1.48      ( r1_subset_1(sK2,sK3) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_28]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1290,plain,
% 7.03/1.48      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_3,plain,
% 7.03/1.48      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 7.03/1.48      | ~ v1_relat_1(X1)
% 7.03/1.48      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.03/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_6,plain,
% 7.03/1.48      ( ~ r1_subset_1(X0,X1)
% 7.03/1.48      | r1_xboole_0(X0,X1)
% 7.03/1.48      | v1_xboole_0(X0)
% 7.03/1.48      | v1_xboole_0(X1) ),
% 7.03/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_468,plain,
% 7.03/1.48      ( ~ r1_subset_1(X0,X1)
% 7.03/1.48      | ~ v1_relat_1(X2)
% 7.03/1.48      | v1_xboole_0(X0)
% 7.03/1.48      | v1_xboole_0(X1)
% 7.03/1.48      | X0 != X3
% 7.03/1.48      | k7_relat_1(X2,X3) = k1_xboole_0
% 7.03/1.48      | k1_relat_1(X2) != X1 ),
% 7.03/1.48      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_469,plain,
% 7.03/1.48      ( ~ r1_subset_1(X0,k1_relat_1(X1))
% 7.03/1.48      | ~ v1_relat_1(X1)
% 7.03/1.48      | v1_xboole_0(X0)
% 7.03/1.48      | v1_xboole_0(k1_relat_1(X1))
% 7.03/1.48      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 7.03/1.48      inference(unflattening,[status(thm)],[c_468]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_748,plain,
% 7.03/1.48      ( ~ r1_subset_1(X0_53,k1_relat_1(X1_53))
% 7.03/1.48      | ~ v1_relat_1(X1_53)
% 7.03/1.48      | v1_xboole_0(X0_53)
% 7.03/1.48      | v1_xboole_0(k1_relat_1(X1_53))
% 7.03/1.48      | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_469]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1300,plain,
% 7.03/1.48      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 7.03/1.48      | r1_subset_1(X1_53,k1_relat_1(X0_53)) != iProver_top
% 7.03/1.48      | v1_relat_1(X0_53) != iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(k1_relat_1(X0_53)) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_3796,plain,
% 7.03/1.48      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 7.03/1.48      | r1_subset_1(X0_53,sK3) != iProver_top
% 7.03/1.48      | v1_relat_1(sK5) != iProver_top
% 7.03/1.48      | v1_xboole_0(X0_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(k1_relat_1(sK5)) = iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_3135,c_1300]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_3814,plain,
% 7.03/1.48      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 7.03/1.48      | r1_subset_1(X0_53,sK3) != iProver_top
% 7.03/1.48      | v1_relat_1(sK5) != iProver_top
% 7.03/1.48      | v1_xboole_0(X0_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.03/1.48      inference(light_normalisation,[status(thm)],[c_3796,c_3135]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1619,plain,
% 7.03/1.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.03/1.48      | v1_relat_1(sK5) ),
% 7.03/1.48      inference(instantiation,[status(thm)],[c_771]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1620,plain,
% 7.03/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.03/1.48      | v1_relat_1(sK5) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_1619]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_4286,plain,
% 7.03/1.48      ( v1_xboole_0(X0_53) = iProver_top
% 7.03/1.48      | k7_relat_1(sK5,X0_53) = k1_xboole_0
% 7.03/1.48      | r1_subset_1(X0_53,sK3) != iProver_top ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_3814,c_39,c_47,c_1620]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_4287,plain,
% 7.03/1.48      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 7.03/1.48      | r1_subset_1(X0_53,sK3) != iProver_top
% 7.03/1.48      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.48      inference(renaming,[status(thm)],[c_4286]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_4295,plain,
% 7.03/1.48      ( k7_relat_1(sK5,sK2) = k1_xboole_0
% 7.03/1.48      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1290,c_4287]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_41,plain,
% 7.03/1.48      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_3824,plain,
% 7.03/1.48      ( k7_relat_1(sK5,sK2) = k1_xboole_0
% 7.03/1.48      | r1_subset_1(sK2,sK3) != iProver_top
% 7.03/1.48      | v1_relat_1(sK5) != iProver_top
% 7.03/1.48      | v1_xboole_0(sK3) = iProver_top
% 7.03/1.48      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.48      inference(instantiation,[status(thm)],[c_3814]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_4298,plain,
% 7.03/1.48      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_4295,c_37,c_39,c_41,c_47,c_1620,c_3824]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_768,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.03/1.48      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.03/1.48      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.03/1.48      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.03/1.48      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.03/1.48      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.03/1.48      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
% 7.03/1.48      | ~ v1_funct_1(X0_53)
% 7.03/1.48      | ~ v1_funct_1(X3_53)
% 7.03/1.48      | v1_xboole_0(X2_53)
% 7.03/1.48      | v1_xboole_0(X1_53)
% 7.03/1.48      | v1_xboole_0(X4_53)
% 7.03/1.48      | v1_xboole_0(X5_53) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_18]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1281,plain,
% 7.03/1.48      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.03/1.48      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.03/1.48      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.03/1.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.03/1.48      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 7.03/1.48      | v1_funct_1(X0_53) != iProver_top
% 7.03/1.48      | v1_funct_1(X3_53) != iProver_top
% 7.03/1.48      | v1_xboole_0(X5_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X2_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X4_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1452,plain,
% 7.03/1.48      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.03/1.48      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.03/1.48      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.03/1.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.03/1.48      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 7.03/1.48      | v1_funct_1(X0_53) != iProver_top
% 7.03/1.48      | v1_funct_1(X3_53) != iProver_top
% 7.03/1.48      | v1_xboole_0(X2_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X4_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top ),
% 7.03/1.48      inference(forward_subsumption_resolution,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_1281,c_1275]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_3953,plain,
% 7.03/1.48      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 7.03/1.48      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 7.03/1.48      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 7.03/1.48      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 7.03/1.48      | v1_funct_1(X5_53) != iProver_top
% 7.03/1.48      | v1_funct_1(X4_53) != iProver_top
% 7.03/1.48      | v1_funct_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53)) != iProver_top
% 7.03/1.48      | v1_xboole_0(X3_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X2_53) = iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1452,c_1279]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_766,plain,
% 7.03/1.48      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.03/1.48      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.03/1.48      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.03/1.48      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.03/1.48      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.03/1.48      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.03/1.48      | ~ v1_funct_1(X0_53)
% 7.03/1.48      | ~ v1_funct_1(X3_53)
% 7.03/1.48      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
% 7.03/1.48      | v1_xboole_0(X2_53)
% 7.03/1.48      | v1_xboole_0(X1_53)
% 7.03/1.48      | v1_xboole_0(X4_53)
% 7.03/1.48      | v1_xboole_0(X5_53) ),
% 7.03/1.48      inference(subtyping,[status(esa)],[c_20]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1283,plain,
% 7.03/1.48      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.03/1.48      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.03/1.48      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.03/1.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.03/1.48      | v1_funct_1(X0_53) != iProver_top
% 7.03/1.48      | v1_funct_1(X3_53) != iProver_top
% 7.03/1.48      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 7.03/1.48      | v1_xboole_0(X5_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X2_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X4_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top ),
% 7.03/1.48      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_1400,plain,
% 7.03/1.48      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 7.03/1.48      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 7.03/1.48      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 7.03/1.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 7.03/1.48      | v1_funct_1(X0_53) != iProver_top
% 7.03/1.48      | v1_funct_1(X3_53) != iProver_top
% 7.03/1.48      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 7.03/1.48      | v1_xboole_0(X2_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X4_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top ),
% 7.03/1.48      inference(forward_subsumption_resolution,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_1283,c_1275]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_8827,plain,
% 7.03/1.48      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 7.03/1.48      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 7.03/1.48      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 7.03/1.48      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 7.03/1.48      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 7.03/1.48      | v1_funct_1(X5_53) != iProver_top
% 7.03/1.48      | v1_funct_1(X4_53) != iProver_top
% 7.03/1.48      | v1_xboole_0(X2_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(X3_53) = iProver_top ),
% 7.03/1.48      inference(forward_subsumption_resolution,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_3953,c_1400]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_8831,plain,
% 7.03/1.48      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.03/1.48      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.03/1.48      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.03/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | v1_funct_1(X2_53) != iProver_top
% 7.03/1.48      | v1_funct_1(sK5) != iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top
% 7.03/1.48      | v1_xboole_0(sK1) = iProver_top
% 7.03/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.03/1.48      inference(superposition,[status(thm)],[c_1284,c_8827]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_8930,plain,
% 7.03/1.48      ( v1_funct_1(X2_53) != iProver_top
% 7.03/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.03/1.48      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.48      | k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.03/1.48      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.03/1.48      | v1_xboole_0(X1_53) = iProver_top ),
% 7.03/1.48      inference(global_propositional_subsumption,
% 7.03/1.48                [status(thm)],
% 7.03/1.48                [c_8831,c_36,c_39,c_45,c_46]) ).
% 7.03/1.48  
% 7.03/1.48  cnf(c_8931,plain,
% 7.03/1.48      ( k2_partfun1(k4_subset_1(X0_53,X1_53,sK3),sK1,k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,X1_53,sK3,X2_53,sK5),X3_53)
% 7.03/1.49      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.03/1.49      | v1_xboole_0(X1_53) = iProver_top ),
% 7.03/1.49      inference(renaming,[status(thm)],[c_8930]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_8944,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.03/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.49      | v1_funct_1(sK4) != iProver_top
% 7.03/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.49      inference(superposition,[status(thm)],[c_1287,c_8931]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_9323,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 7.03/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_8944,c_37,c_42,c_43]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_9332,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
% 7.03/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.03/1.49      inference(superposition,[status(thm)],[c_1291,c_9323]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_31,negated_conjecture,
% 7.03/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.03/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_38,plain,
% 7.03/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.03/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_9337,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_9332,c_38]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_18354,plain,
% 7.03/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.03/1.49      | k7_relat_1(sK4,sK3) != k1_xboole_0
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.03/1.49      inference(demodulation,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_18353,c_1927,c_3138,c_3267,c_4298,c_9337]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_7,plain,
% 7.03/1.49      ( ~ r1_subset_1(X0,X1)
% 7.03/1.49      | r1_subset_1(X1,X0)
% 7.03/1.49      | v1_xboole_0(X0)
% 7.03/1.49      | v1_xboole_0(X1) ),
% 7.03/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_772,plain,
% 7.03/1.49      ( ~ r1_subset_1(X0_53,X1_53)
% 7.03/1.49      | r1_subset_1(X1_53,X0_53)
% 7.03/1.49      | v1_xboole_0(X0_53)
% 7.03/1.49      | v1_xboole_0(X1_53) ),
% 7.03/1.49      inference(subtyping,[status(esa)],[c_7]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_1277,plain,
% 7.03/1.49      ( r1_subset_1(X0_53,X1_53) != iProver_top
% 7.03/1.49      | r1_subset_1(X1_53,X0_53) = iProver_top
% 7.03/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.49      inference(predicate_to_equality,[status(thm)],[c_772]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_2300,plain,
% 7.03/1.49      ( r1_subset_1(sK3,sK2) = iProver_top
% 7.03/1.49      | v1_xboole_0(sK3) = iProver_top
% 7.03/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.49      inference(superposition,[status(thm)],[c_1290,c_1277]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_1639,plain,
% 7.03/1.49      ( r1_subset_1(sK3,sK2)
% 7.03/1.49      | ~ r1_subset_1(sK2,sK3)
% 7.03/1.49      | v1_xboole_0(sK3)
% 7.03/1.49      | v1_xboole_0(sK2) ),
% 7.03/1.49      inference(instantiation,[status(thm)],[c_772]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_1640,plain,
% 7.03/1.49      ( r1_subset_1(sK3,sK2) = iProver_top
% 7.03/1.49      | r1_subset_1(sK2,sK3) != iProver_top
% 7.03/1.49      | v1_xboole_0(sK3) = iProver_top
% 7.03/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.49      inference(predicate_to_equality,[status(thm)],[c_1639]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_2583,plain,
% 7.03/1.49      ( r1_subset_1(sK3,sK2) = iProver_top ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_2300,c_37,c_39,c_41,c_1640]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_3797,plain,
% 7.03/1.49      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 7.03/1.49      | r1_subset_1(X0_53,sK2) != iProver_top
% 7.03/1.49      | v1_relat_1(sK4) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.03/1.49      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
% 7.03/1.49      inference(superposition,[status(thm)],[c_3263,c_1300]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_3803,plain,
% 7.03/1.49      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 7.03/1.49      | r1_subset_1(X0_53,sK2) != iProver_top
% 7.03/1.49      | v1_relat_1(sK4) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.03/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.49      inference(light_normalisation,[status(thm)],[c_3797,c_3263]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_1622,plain,
% 7.03/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.03/1.49      | v1_relat_1(sK4) ),
% 7.03/1.49      inference(instantiation,[status(thm)],[c_771]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_1623,plain,
% 7.03/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.03/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.03/1.49      inference(predicate_to_equality,[status(thm)],[c_1622]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_4236,plain,
% 7.03/1.49      ( v1_xboole_0(X0_53) = iProver_top
% 7.03/1.49      | k7_relat_1(sK4,X0_53) = k1_xboole_0
% 7.03/1.49      | r1_subset_1(X0_53,sK2) != iProver_top ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_3803,c_37,c_44,c_1623]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_4237,plain,
% 7.03/1.49      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 7.03/1.49      | r1_subset_1(X0_53,sK2) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.49      inference(renaming,[status(thm)],[c_4236]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_4245,plain,
% 7.03/1.49      ( k7_relat_1(sK4,sK3) = k1_xboole_0
% 7.03/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.03/1.49      inference(superposition,[status(thm)],[c_2583,c_4237]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_4248,plain,
% 7.03/1.49      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_4245,c_39]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_18355,plain,
% 7.03/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.03/1.49      | k1_xboole_0 != k1_xboole_0
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.03/1.49      inference(light_normalisation,[status(thm)],[c_18354,c_4248]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_18356,plain,
% 7.03/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.03/1.49      inference(equality_resolution_simp,[status(thm)],[c_18355]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_17,plain,
% 7.03/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.03/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.03/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.03/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.03/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.03/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.03/1.49      | ~ v1_funct_1(X0)
% 7.03/1.49      | ~ v1_funct_1(X3)
% 7.03/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.03/1.49      | v1_xboole_0(X5)
% 7.03/1.49      | v1_xboole_0(X2)
% 7.03/1.49      | v1_xboole_0(X4)
% 7.03/1.49      | v1_xboole_0(X1)
% 7.03/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.03/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.03/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_184,plain,
% 7.03/1.49      ( ~ v1_funct_1(X3)
% 7.03/1.49      | ~ v1_funct_1(X0)
% 7.03/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.03/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.03/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.03/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.03/1.49      | v1_xboole_0(X5)
% 7.03/1.49      | v1_xboole_0(X2)
% 7.03/1.49      | v1_xboole_0(X4)
% 7.03/1.49      | v1_xboole_0(X1)
% 7.03/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.03/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_17,c_20,c_19,c_18]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_185,plain,
% 7.03/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.03/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.03/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.03/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.03/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.03/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.03/1.49      | ~ v1_funct_1(X0)
% 7.03/1.49      | ~ v1_funct_1(X3)
% 7.03/1.49      | v1_xboole_0(X1)
% 7.03/1.49      | v1_xboole_0(X2)
% 7.03/1.49      | v1_xboole_0(X4)
% 7.03/1.49      | v1_xboole_0(X5)
% 7.03/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.03/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.03/1.49      inference(renaming,[status(thm)],[c_184]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_751,plain,
% 7.03/1.49      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 7.03/1.49      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 7.03/1.49      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 7.03/1.49      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 7.03/1.49      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 7.03/1.49      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 7.03/1.49      | ~ v1_funct_1(X0_53)
% 7.03/1.49      | ~ v1_funct_1(X3_53)
% 7.03/1.49      | v1_xboole_0(X2_53)
% 7.03/1.49      | v1_xboole_0(X1_53)
% 7.03/1.49      | v1_xboole_0(X4_53)
% 7.03/1.49      | v1_xboole_0(X5_53)
% 7.03/1.49      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 7.03/1.49      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 7.03/1.49      inference(subtyping,[status(esa)],[c_185]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_1297,plain,
% 7.03/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 7.03/1.49      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 7.03/1.49      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.03/1.49      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.03/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.03/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.03/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.03/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.03/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.03/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.03/1.49      | v1_xboole_0(X3_53) = iProver_top
% 7.03/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.03/1.49      | v1_xboole_0(X4_53) = iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.49      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_1479,plain,
% 7.03/1.49      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 7.03/1.49      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X0_53) = X2_53
% 7.03/1.49      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 7.03/1.49      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 7.03/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.03/1.49      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 7.03/1.49      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 7.03/1.49      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 7.03/1.49      | v1_funct_1(X5_53) != iProver_top
% 7.03/1.49      | v1_funct_1(X2_53) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.03/1.49      | v1_xboole_0(X1_53) = iProver_top
% 7.03/1.49      | v1_xboole_0(X4_53) = iProver_top ),
% 7.03/1.49      inference(forward_subsumption_resolution,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_1297,c_1275]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_4734,plain,
% 7.03/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.03/1.49      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.03/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.03/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.03/1.49      | v1_funct_1(sK5) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top
% 7.03/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.03/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.03/1.49      inference(superposition,[status(thm)],[c_2511,c_1479]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15368,plain,
% 7.03/1.49      ( v1_funct_1(X1_53) != iProver_top
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.03/1.49      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.03/1.49      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.03/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_4734,c_36,c_39,c_45,c_46,c_47]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15369,plain,
% 7.03/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 7.03/1.49      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.03/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 7.03/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.49      inference(renaming,[status(thm)],[c_15368]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15388,plain,
% 7.03/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_53,sK3))
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.03/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.49      inference(superposition,[status(thm)],[c_1927,c_15369]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15397,plain,
% 7.03/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,X0_53)
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.03/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.49      inference(light_normalisation,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_15388,c_1927,c_3138]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_40,plain,
% 7.03/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.03/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15579,plain,
% 7.03/1.49      ( m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.03/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.03/1.49      | k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,X0_53)
% 7.03/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_15397,c_40]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15580,plain,
% 7.03/1.49      ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,X0_53)
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 7.03/1.49      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | v1_funct_1(X1_53) != iProver_top
% 7.03/1.49      | v1_xboole_0(X0_53) = iProver_top ),
% 7.03/1.49      inference(renaming,[status(thm)],[c_15579]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15593,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.03/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,sK2)
% 7.03/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | v1_funct_1(sK4) != iProver_top
% 7.03/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.49      inference(superposition,[status(thm)],[c_2517,c_15580]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15681,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.03/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.03/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | v1_funct_1(sK4) != iProver_top
% 7.03/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.49      inference(light_normalisation,[status(thm)],[c_15593,c_4298]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15682,plain,
% 7.03/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.03/1.49      | k1_xboole_0 != k1_xboole_0
% 7.03/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | v1_funct_1(sK4) != iProver_top
% 7.03/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.49      inference(demodulation,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_15681,c_3267,c_4248,c_9337]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_15683,plain,
% 7.03/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.03/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.03/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.03/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.03/1.49      | v1_funct_1(sK4) != iProver_top
% 7.03/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.03/1.49      inference(equality_resolution_simp,[status(thm)],[c_15682]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_21,negated_conjecture,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.03/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.03/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_765,negated_conjecture,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.03/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.03/1.49      inference(subtyping,[status(esa)],[c_21]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_2092,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.03/1.49      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.03/1.49      inference(demodulation,[status(thm)],[c_1927,c_765]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_2515,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.03/1.49      | k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.03/1.49      inference(demodulation,[status(thm)],[c_2511,c_2092]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_2578,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.03/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) ),
% 7.03/1.49      inference(demodulation,[status(thm)],[c_2515,c_2517]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_3274,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.03/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,sK2) ),
% 7.03/1.49      inference(demodulation,[status(thm)],[c_3138,c_2578]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_3671,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.03/1.49      | k7_relat_1(sK4,sK3) != k7_relat_1(sK5,sK2) ),
% 7.03/1.49      inference(demodulation,[status(thm)],[c_3274,c_3267]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_4251,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.03/1.49      | k7_relat_1(sK5,sK2) != k1_xboole_0 ),
% 7.03/1.49      inference(demodulation,[status(thm)],[c_4248,c_3671]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_4351,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.03/1.49      inference(global_propositional_subsumption,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_4251,c_37,c_39,c_41,c_47,c_1620,c_3824]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_4352,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.03/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.03/1.49      inference(renaming,[status(thm)],[c_4351]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_9341,plain,
% 7.03/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.03/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.03/1.49      inference(demodulation,[status(thm)],[c_9337,c_4352]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(c_9342,plain,
% 7.03/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.03/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.03/1.49      inference(demodulation,[status(thm)],[c_9341,c_9337]) ).
% 7.03/1.49  
% 7.03/1.49  cnf(contradiction,plain,
% 7.03/1.49      ( $false ),
% 7.03/1.49      inference(minisat,
% 7.03/1.49                [status(thm)],
% 7.03/1.49                [c_18356,c_15683,c_9342,c_44,c_43,c_42,c_40,c_38,c_37]) ).
% 7.03/1.49  
% 7.03/1.49  
% 7.03/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.03/1.49  
% 7.03/1.49  ------                               Statistics
% 7.03/1.49  
% 7.03/1.49  ------ General
% 7.03/1.49  
% 7.03/1.49  abstr_ref_over_cycles:                  0
% 7.03/1.49  abstr_ref_under_cycles:                 0
% 7.03/1.49  gc_basic_clause_elim:                   0
% 7.03/1.49  forced_gc_time:                         0
% 7.03/1.49  parsing_time:                           0.011
% 7.03/1.49  unif_index_cands_time:                  0.
% 7.03/1.49  unif_index_add_time:                    0.
% 7.03/1.49  orderings_time:                         0.
% 7.03/1.49  out_proof_time:                         0.021
% 7.03/1.49  total_time:                             0.967
% 7.03/1.49  num_of_symbols:                         58
% 7.03/1.49  num_of_terms:                           34536
% 7.03/1.49  
% 7.03/1.49  ------ Preprocessing
% 7.03/1.49  
% 7.03/1.49  num_of_splits:                          0
% 7.03/1.49  num_of_split_atoms:                     0
% 7.03/1.49  num_of_reused_defs:                     0
% 7.03/1.49  num_eq_ax_congr_red:                    15
% 7.03/1.49  num_of_sem_filtered_clauses:            1
% 7.03/1.49  num_of_subtypes:                        2
% 7.03/1.49  monotx_restored_types:                  0
% 7.03/1.49  sat_num_of_epr_types:                   0
% 7.03/1.49  sat_num_of_non_cyclic_types:            0
% 7.03/1.49  sat_guarded_non_collapsed_types:        1
% 7.03/1.49  num_pure_diseq_elim:                    0
% 7.03/1.49  simp_replaced_by:                       0
% 7.03/1.49  res_preprocessed:                       154
% 7.03/1.49  prep_upred:                             0
% 7.03/1.49  prep_unflattend:                        9
% 7.03/1.49  smt_new_axioms:                         0
% 7.03/1.49  pred_elim_cands:                        6
% 7.03/1.49  pred_elim:                              3
% 7.03/1.49  pred_elim_cl:                           5
% 7.03/1.49  pred_elim_cycles:                       6
% 7.03/1.49  merged_defs:                            0
% 7.03/1.49  merged_defs_ncl:                        0
% 7.03/1.49  bin_hyper_res:                          0
% 7.03/1.49  prep_cycles:                            4
% 7.03/1.49  pred_elim_time:                         0.005
% 7.03/1.49  splitting_time:                         0.
% 7.03/1.49  sem_filter_time:                        0.
% 7.03/1.49  monotx_time:                            0.
% 7.03/1.49  subtype_inf_time:                       0.001
% 7.03/1.49  
% 7.03/1.49  ------ Problem properties
% 7.03/1.49  
% 7.03/1.49  clauses:                                29
% 7.03/1.49  conjectures:                            14
% 7.03/1.49  epr:                                    10
% 7.03/1.49  horn:                                   20
% 7.03/1.49  ground:                                 14
% 7.03/1.49  unary:                                  14
% 7.03/1.49  binary:                                 3
% 7.03/1.49  lits:                                   127
% 7.03/1.49  lits_eq:                                15
% 7.03/1.49  fd_pure:                                0
% 7.03/1.49  fd_pseudo:                              0
% 7.03/1.49  fd_cond:                                0
% 7.03/1.49  fd_pseudo_cond:                         1
% 7.03/1.49  ac_symbols:                             0
% 7.03/1.49  
% 7.03/1.49  ------ Propositional Solver
% 7.03/1.49  
% 7.03/1.49  prop_solver_calls:                      30
% 7.03/1.49  prop_fast_solver_calls:                 2599
% 7.03/1.49  smt_solver_calls:                       0
% 7.03/1.49  smt_fast_solver_calls:                  0
% 7.03/1.49  prop_num_of_clauses:                    7307
% 7.03/1.49  prop_preprocess_simplified:             15169
% 7.03/1.49  prop_fo_subsumed:                       203
% 7.03/1.49  prop_solver_time:                       0.
% 7.03/1.49  smt_solver_time:                        0.
% 7.03/1.49  smt_fast_solver_time:                   0.
% 7.03/1.49  prop_fast_solver_time:                  0.
% 7.03/1.49  prop_unsat_core_time:                   0.
% 7.03/1.49  
% 7.03/1.49  ------ QBF
% 7.03/1.49  
% 7.03/1.49  qbf_q_res:                              0
% 7.03/1.49  qbf_num_tautologies:                    0
% 7.03/1.49  qbf_prep_cycles:                        0
% 7.03/1.49  
% 7.03/1.49  ------ BMC1
% 7.03/1.49  
% 7.03/1.49  bmc1_current_bound:                     -1
% 7.03/1.49  bmc1_last_solved_bound:                 -1
% 7.03/1.49  bmc1_unsat_core_size:                   -1
% 7.03/1.49  bmc1_unsat_core_parents_size:           -1
% 7.03/1.49  bmc1_merge_next_fun:                    0
% 7.03/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.03/1.49  
% 7.03/1.49  ------ Instantiation
% 7.03/1.49  
% 7.03/1.49  inst_num_of_clauses:                    1755
% 7.03/1.49  inst_num_in_passive:                    810
% 7.03/1.49  inst_num_in_active:                     807
% 7.03/1.49  inst_num_in_unprocessed:                138
% 7.03/1.49  inst_num_of_loops:                      820
% 7.03/1.49  inst_num_of_learning_restarts:          0
% 7.03/1.49  inst_num_moves_active_passive:          7
% 7.03/1.49  inst_lit_activity:                      0
% 7.03/1.49  inst_lit_activity_moves:                0
% 7.03/1.49  inst_num_tautologies:                   0
% 7.03/1.49  inst_num_prop_implied:                  0
% 7.03/1.49  inst_num_existing_simplified:           0
% 7.03/1.49  inst_num_eq_res_simplified:             0
% 7.03/1.49  inst_num_child_elim:                    0
% 7.03/1.49  inst_num_of_dismatching_blockings:      220
% 7.03/1.49  inst_num_of_non_proper_insts:           1442
% 7.03/1.49  inst_num_of_duplicates:                 0
% 7.03/1.49  inst_inst_num_from_inst_to_res:         0
% 7.03/1.49  inst_dismatching_checking_time:         0.
% 7.03/1.49  
% 7.03/1.49  ------ Resolution
% 7.03/1.49  
% 7.03/1.49  res_num_of_clauses:                     0
% 7.03/1.49  res_num_in_passive:                     0
% 7.03/1.49  res_num_in_active:                      0
% 7.03/1.49  res_num_of_loops:                       158
% 7.03/1.49  res_forward_subset_subsumed:            49
% 7.03/1.49  res_backward_subset_subsumed:           4
% 7.03/1.49  res_forward_subsumed:                   0
% 7.03/1.49  res_backward_subsumed:                  0
% 7.03/1.49  res_forward_subsumption_resolution:     1
% 7.03/1.49  res_backward_subsumption_resolution:    0
% 7.03/1.49  res_clause_to_clause_subsumption:       1662
% 7.03/1.49  res_orphan_elimination:                 0
% 7.03/1.49  res_tautology_del:                      37
% 7.03/1.49  res_num_eq_res_simplified:              0
% 7.03/1.49  res_num_sel_changes:                    0
% 7.03/1.49  res_moves_from_active_to_pass:          0
% 7.03/1.49  
% 7.03/1.49  ------ Superposition
% 7.03/1.49  
% 7.03/1.49  sup_time_total:                         0.
% 7.03/1.49  sup_time_generating:                    0.
% 7.03/1.49  sup_time_sim_full:                      0.
% 7.03/1.49  sup_time_sim_immed:                     0.
% 7.03/1.49  
% 7.03/1.49  sup_num_of_clauses:                     283
% 7.03/1.49  sup_num_in_active:                      146
% 7.03/1.49  sup_num_in_passive:                     137
% 7.03/1.49  sup_num_of_loops:                       162
% 7.03/1.49  sup_fw_superposition:                   345
% 7.03/1.49  sup_bw_superposition:                   49
% 7.03/1.49  sup_immediate_simplified:               174
% 7.03/1.49  sup_given_eliminated:                   0
% 7.03/1.49  comparisons_done:                       0
% 7.03/1.49  comparisons_avoided:                    0
% 7.03/1.49  
% 7.03/1.49  ------ Simplifications
% 7.03/1.49  
% 7.03/1.49  
% 7.03/1.49  sim_fw_subset_subsumed:                 7
% 7.03/1.49  sim_bw_subset_subsumed:                 0
% 7.03/1.49  sim_fw_subsumed:                        17
% 7.03/1.49  sim_bw_subsumed:                        8
% 7.03/1.49  sim_fw_subsumption_res:                 11
% 7.03/1.49  sim_bw_subsumption_res:                 0
% 7.03/1.49  sim_tautology_del:                      0
% 7.03/1.49  sim_eq_tautology_del:                   0
% 7.03/1.49  sim_eq_res_simp:                        11
% 7.03/1.49  sim_fw_demodulated:                     117
% 7.03/1.49  sim_bw_demodulated:                     17
% 7.03/1.49  sim_light_normalised:                   49
% 7.03/1.49  sim_joinable_taut:                      0
% 7.03/1.49  sim_joinable_simp:                      0
% 7.03/1.49  sim_ac_normalised:                      0
% 7.03/1.49  sim_smt_subsumption:                    0
% 7.03/1.49  
%------------------------------------------------------------------------------
