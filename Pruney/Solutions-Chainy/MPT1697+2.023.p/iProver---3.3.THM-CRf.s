%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:26 EST 2020

% Result     : Theorem 7.19s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :  205 (2613 expanded)
%              Number of clauses        :  133 ( 656 expanded)
%              Number of leaves         :   18 (1030 expanded)
%              Depth                    :   23
%              Number of atoms          : 1169 (33688 expanded)
%              Number of equality atoms :  474 (7999 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f39])).

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f51,f50,f49,f48,f47,f46])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f85,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f88,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f35])).

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
    inference(nnf_transformation,[],[f36])).

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
    inference(flattening,[],[f44])).

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
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f37])).

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
    inference(cnf_transformation,[],[f38])).

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
    inference(cnf_transformation,[],[f38])).

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
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f80,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f78,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
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

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f82,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f58,f57])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

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
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f52])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1023,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1544,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1023])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1039,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | k9_subset_1(X1_54,X2_54,X0_54) = k1_setfam_1(k2_tarski(X2_54,X0_54)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1529,plain,
    ( k9_subset_1(X0_54,X1_54,X2_54) = k1_setfam_1(k2_tarski(X1_54,X2_54))
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1039])).

cnf(c_2624,plain,
    ( k9_subset_1(sK0,X0_54,sK3) = k1_setfam_1(k2_tarski(X0_54,sK3)) ),
    inference(superposition,[status(thm)],[c_1544,c_1529])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1026,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1541,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1026])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1035,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1533,plain,
    ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1035])).

cnf(c_2812,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1533])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3429,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2812,c_43])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1029,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1538,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1029])).

cnf(c_2811,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_1533])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_46,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3425,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2811,c_46])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_21,plain,
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

cnf(c_20,plain,
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

cnf(c_19,plain,
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

cnf(c_203,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_21,c_20,c_19])).

cnf(c_204,plain,
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
    inference(renaming,[status(thm)],[c_203])).

cnf(c_1016,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
    inference(subtyping,[status(esa)],[c_204])).

cnf(c_1551,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_5590,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3425,c_1551])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_40,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_47,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_48,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10791,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5590,c_37,c_40,c_46,c_47,c_48])).

cnf(c_10792,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_10791])).

cnf(c_10798,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3429,c_10792])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_38,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_44,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1038,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_xboole_0(X1_54)
    | v1_xboole_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1719,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_54))
    | ~ v1_xboole_0(X0_54)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1720,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1719])).

cnf(c_10860,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10798,c_38,c_43,c_44,c_45,c_1720])).

cnf(c_10861,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10860])).

cnf(c_10866,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2624,c_10861])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_265,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_557,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_558,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_560,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_33,c_31])).

cnf(c_644,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_265,c_560])).

cnf(c_645,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_1011,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_645])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1036,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1532,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1036])).

cnf(c_2421,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_1532])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1037,plain,
    ( ~ v1_relat_1(X0_54)
    | k7_relat_1(X0_54,k1_setfam_1(k2_tarski(X1_54,X2_54))) = k7_relat_1(k7_relat_1(X0_54,X1_54),X2_54) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1531,plain,
    ( k7_relat_1(X0_54,k1_setfam_1(k2_tarski(X1_54,X2_54))) = k7_relat_1(k7_relat_1(X0_54,X1_54),X2_54)
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_2722,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0_54,X1_54))) = k7_relat_1(k7_relat_1(sK5,X0_54),X1_54) ),
    inference(superposition,[status(thm)],[c_2421,c_1531])).

cnf(c_3595,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1011,c_2722])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_632,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
    | sK3 != X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_560])).

cnf(c_633,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,sK2),sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_1012,plain,
    ( ~ v1_relat_1(X0_54)
    | k7_relat_1(k7_relat_1(X0_54,sK2),sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_633])).

cnf(c_1555,plain,
    ( k7_relat_1(k7_relat_1(X0_54,sK2),sK3) = k1_xboole_0
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1012])).

cnf(c_2426,plain,
    ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2421,c_1555])).

cnf(c_3596,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3595,c_2426])).

cnf(c_10867,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10866,c_1011,c_3596])).

cnf(c_2422,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_1532])).

cnf(c_2723,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0_54,X1_54))) = k7_relat_1(k7_relat_1(sK4,X0_54),X1_54) ),
    inference(superposition,[status(thm)],[c_2422,c_1531])).

cnf(c_1031,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1537,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
    | v1_xboole_0(X5_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1031])).

cnf(c_1033,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1535,plain,
    ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
    | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
    | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(X3_54) != iProver_top
    | v1_xboole_0(X5_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X4_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1033])).

cnf(c_3581,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
    | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
    | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54)) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1533])).

cnf(c_6311,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
    | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
    | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
    | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
    | v1_funct_1(X5_54) != iProver_top
    | v1_funct_1(X4_54) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X3_54) = iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(superposition,[status(thm)],[c_1537,c_3581])).

cnf(c_6603,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1538,c_6311])).

cnf(c_1758,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0_54))
    | ~ v1_xboole_0(X0_54)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1038])).

cnf(c_1759,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_xboole_0(X0_54) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1758])).

cnf(c_6616,plain,
    ( v1_xboole_0(X1_54) = iProver_top
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6603,c_37,c_40,c_46,c_47,c_1759])).

cnf(c_6617,plain,
    ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
    | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(X2_54) != iProver_top
    | v1_xboole_0(X1_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_6616])).

cnf(c_6623,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1541,c_6617])).

cnf(c_6701,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6623,c_38,c_43,c_44])).

cnf(c_6707,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_6701])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_6712,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6707,c_39])).

cnf(c_10868,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(k7_relat_1(sK4,sK2),sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10867,c_2624,c_2723,c_6712])).

cnf(c_2528,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2422,c_1555])).

cnf(c_10869,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10868,c_2528])).

cnf(c_10870,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10869])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_196,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_21,c_20,c_19])).

cnf(c_197,plain,
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
    inference(renaming,[status(thm)],[c_196])).

cnf(c_1017,plain,
    ( ~ v1_funct_2(X0_54,X1_54,X2_54)
    | ~ v1_funct_2(X3_54,X4_54,X2_54)
    | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
    | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X3_54)
    | v1_xboole_0(X2_54)
    | v1_xboole_0(X1_54)
    | v1_xboole_0(X4_54)
    | v1_xboole_0(X5_54)
    | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
    | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
    inference(subtyping,[status(esa)],[c_197])).

cnf(c_1550,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_1017])).

cnf(c_3828,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3425,c_1550])).

cnf(c_6481,plain,
    ( v1_funct_1(X1_54) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(X2_54) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3828,c_37,c_40,c_46,c_47,c_48])).

cnf(c_6482,plain,
    ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
    | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
    | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
    | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_xboole_0(X2_54) = iProver_top
    | v1_xboole_0(X0_54) = iProver_top ),
    inference(renaming,[status(thm)],[c_6481])).

cnf(c_6488,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_54) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3429,c_6482])).

cnf(c_8944,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6488,c_38,c_43,c_44,c_45,c_1720])).

cnf(c_8945,plain,
    ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8944])).

cnf(c_8950,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2624,c_8945])).

cnf(c_8951,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8950,c_1011,c_3596])).

cnf(c_8952,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(k7_relat_1(sK4,sK2),sK3) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8951,c_2624,c_2723,c_6712])).

cnf(c_8953,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8952,c_2528])).

cnf(c_8954,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8953])).

cnf(c_22,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1030,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2857,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_2624,c_1030])).

cnf(c_2858,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2857,c_1011])).

cnf(c_3609,plain,
    ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1011,c_2723])).

cnf(c_3610,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3609,c_2528])).

cnf(c_3611,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2858,c_3425,c_3429,c_3596,c_3610])).

cnf(c_3612,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_3611])).

cnf(c_6715,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_6712,c_3612])).

cnf(c_6716,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_6715,c_6712])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10870,c_8954,c_6716,c_41,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:40:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.19/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.19/1.48  
% 7.19/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.19/1.48  
% 7.19/1.48  ------  iProver source info
% 7.19/1.48  
% 7.19/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.19/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.19/1.48  git: non_committed_changes: false
% 7.19/1.48  git: last_make_outside_of_git: false
% 7.19/1.48  
% 7.19/1.48  ------ 
% 7.19/1.48  
% 7.19/1.48  ------ Input Options
% 7.19/1.48  
% 7.19/1.48  --out_options                           all
% 7.19/1.48  --tptp_safe_out                         true
% 7.19/1.48  --problem_path                          ""
% 7.19/1.48  --include_path                          ""
% 7.19/1.48  --clausifier                            res/vclausify_rel
% 7.19/1.48  --clausifier_options                    ""
% 7.19/1.48  --stdin                                 false
% 7.19/1.48  --stats_out                             all
% 7.19/1.48  
% 7.19/1.48  ------ General Options
% 7.19/1.48  
% 7.19/1.48  --fof                                   false
% 7.19/1.48  --time_out_real                         305.
% 7.19/1.48  --time_out_virtual                      -1.
% 7.19/1.48  --symbol_type_check                     false
% 7.19/1.48  --clausify_out                          false
% 7.19/1.48  --sig_cnt_out                           false
% 7.19/1.48  --trig_cnt_out                          false
% 7.19/1.48  --trig_cnt_out_tolerance                1.
% 7.19/1.48  --trig_cnt_out_sk_spl                   false
% 7.19/1.48  --abstr_cl_out                          false
% 7.19/1.48  
% 7.19/1.48  ------ Global Options
% 7.19/1.48  
% 7.19/1.48  --schedule                              default
% 7.19/1.48  --add_important_lit                     false
% 7.19/1.48  --prop_solver_per_cl                    1000
% 7.19/1.48  --min_unsat_core                        false
% 7.19/1.48  --soft_assumptions                      false
% 7.19/1.48  --soft_lemma_size                       3
% 7.19/1.48  --prop_impl_unit_size                   0
% 7.19/1.48  --prop_impl_unit                        []
% 7.19/1.48  --share_sel_clauses                     true
% 7.19/1.48  --reset_solvers                         false
% 7.19/1.48  --bc_imp_inh                            [conj_cone]
% 7.19/1.48  --conj_cone_tolerance                   3.
% 7.19/1.48  --extra_neg_conj                        none
% 7.19/1.48  --large_theory_mode                     true
% 7.19/1.48  --prolific_symb_bound                   200
% 7.19/1.48  --lt_threshold                          2000
% 7.19/1.48  --clause_weak_htbl                      true
% 7.19/1.48  --gc_record_bc_elim                     false
% 7.19/1.48  
% 7.19/1.48  ------ Preprocessing Options
% 7.19/1.48  
% 7.19/1.48  --preprocessing_flag                    true
% 7.19/1.48  --time_out_prep_mult                    0.1
% 7.19/1.48  --splitting_mode                        input
% 7.19/1.48  --splitting_grd                         true
% 7.19/1.48  --splitting_cvd                         false
% 7.19/1.48  --splitting_cvd_svl                     false
% 7.19/1.48  --splitting_nvd                         32
% 7.19/1.48  --sub_typing                            true
% 7.19/1.48  --prep_gs_sim                           true
% 7.19/1.48  --prep_unflatten                        true
% 7.19/1.48  --prep_res_sim                          true
% 7.19/1.48  --prep_upred                            true
% 7.19/1.48  --prep_sem_filter                       exhaustive
% 7.19/1.48  --prep_sem_filter_out                   false
% 7.19/1.48  --pred_elim                             true
% 7.19/1.48  --res_sim_input                         true
% 7.19/1.48  --eq_ax_congr_red                       true
% 7.19/1.48  --pure_diseq_elim                       true
% 7.19/1.48  --brand_transform                       false
% 7.19/1.48  --non_eq_to_eq                          false
% 7.19/1.48  --prep_def_merge                        true
% 7.19/1.48  --prep_def_merge_prop_impl              false
% 7.19/1.48  --prep_def_merge_mbd                    true
% 7.19/1.48  --prep_def_merge_tr_red                 false
% 7.19/1.48  --prep_def_merge_tr_cl                  false
% 7.19/1.48  --smt_preprocessing                     true
% 7.19/1.48  --smt_ac_axioms                         fast
% 7.19/1.48  --preprocessed_out                      false
% 7.19/1.48  --preprocessed_stats                    false
% 7.19/1.48  
% 7.19/1.48  ------ Abstraction refinement Options
% 7.19/1.48  
% 7.19/1.48  --abstr_ref                             []
% 7.19/1.48  --abstr_ref_prep                        false
% 7.19/1.48  --abstr_ref_until_sat                   false
% 7.19/1.48  --abstr_ref_sig_restrict                funpre
% 7.19/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.19/1.48  --abstr_ref_under                       []
% 7.19/1.48  
% 7.19/1.48  ------ SAT Options
% 7.19/1.48  
% 7.19/1.48  --sat_mode                              false
% 7.19/1.48  --sat_fm_restart_options                ""
% 7.19/1.48  --sat_gr_def                            false
% 7.19/1.48  --sat_epr_types                         true
% 7.19/1.48  --sat_non_cyclic_types                  false
% 7.19/1.48  --sat_finite_models                     false
% 7.19/1.48  --sat_fm_lemmas                         false
% 7.19/1.48  --sat_fm_prep                           false
% 7.19/1.48  --sat_fm_uc_incr                        true
% 7.19/1.48  --sat_out_model                         small
% 7.19/1.48  --sat_out_clauses                       false
% 7.19/1.48  
% 7.19/1.48  ------ QBF Options
% 7.19/1.48  
% 7.19/1.48  --qbf_mode                              false
% 7.19/1.48  --qbf_elim_univ                         false
% 7.19/1.48  --qbf_dom_inst                          none
% 7.19/1.48  --qbf_dom_pre_inst                      false
% 7.19/1.48  --qbf_sk_in                             false
% 7.19/1.48  --qbf_pred_elim                         true
% 7.19/1.48  --qbf_split                             512
% 7.19/1.48  
% 7.19/1.48  ------ BMC1 Options
% 7.19/1.48  
% 7.19/1.48  --bmc1_incremental                      false
% 7.19/1.48  --bmc1_axioms                           reachable_all
% 7.19/1.48  --bmc1_min_bound                        0
% 7.19/1.48  --bmc1_max_bound                        -1
% 7.19/1.48  --bmc1_max_bound_default                -1
% 7.19/1.48  --bmc1_symbol_reachability              true
% 7.19/1.48  --bmc1_property_lemmas                  false
% 7.19/1.48  --bmc1_k_induction                      false
% 7.19/1.48  --bmc1_non_equiv_states                 false
% 7.19/1.48  --bmc1_deadlock                         false
% 7.19/1.48  --bmc1_ucm                              false
% 7.19/1.48  --bmc1_add_unsat_core                   none
% 7.19/1.48  --bmc1_unsat_core_children              false
% 7.19/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.19/1.48  --bmc1_out_stat                         full
% 7.19/1.48  --bmc1_ground_init                      false
% 7.19/1.48  --bmc1_pre_inst_next_state              false
% 7.19/1.48  --bmc1_pre_inst_state                   false
% 7.19/1.48  --bmc1_pre_inst_reach_state             false
% 7.19/1.48  --bmc1_out_unsat_core                   false
% 7.19/1.48  --bmc1_aig_witness_out                  false
% 7.19/1.48  --bmc1_verbose                          false
% 7.19/1.48  --bmc1_dump_clauses_tptp                false
% 7.19/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.19/1.48  --bmc1_dump_file                        -
% 7.19/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.19/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.19/1.48  --bmc1_ucm_extend_mode                  1
% 7.19/1.48  --bmc1_ucm_init_mode                    2
% 7.19/1.48  --bmc1_ucm_cone_mode                    none
% 7.19/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.19/1.48  --bmc1_ucm_relax_model                  4
% 7.19/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.19/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.19/1.48  --bmc1_ucm_layered_model                none
% 7.19/1.48  --bmc1_ucm_max_lemma_size               10
% 7.19/1.48  
% 7.19/1.48  ------ AIG Options
% 7.19/1.48  
% 7.19/1.48  --aig_mode                              false
% 7.19/1.48  
% 7.19/1.48  ------ Instantiation Options
% 7.19/1.48  
% 7.19/1.48  --instantiation_flag                    true
% 7.19/1.48  --inst_sos_flag                         true
% 7.19/1.48  --inst_sos_phase                        true
% 7.19/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.19/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.19/1.48  --inst_lit_sel_side                     num_symb
% 7.19/1.48  --inst_solver_per_active                1400
% 7.19/1.48  --inst_solver_calls_frac                1.
% 7.19/1.48  --inst_passive_queue_type               priority_queues
% 7.19/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.19/1.48  --inst_passive_queues_freq              [25;2]
% 7.19/1.48  --inst_dismatching                      true
% 7.19/1.48  --inst_eager_unprocessed_to_passive     true
% 7.19/1.48  --inst_prop_sim_given                   true
% 7.19/1.48  --inst_prop_sim_new                     false
% 7.19/1.48  --inst_subs_new                         false
% 7.19/1.48  --inst_eq_res_simp                      false
% 7.19/1.48  --inst_subs_given                       false
% 7.19/1.48  --inst_orphan_elimination               true
% 7.19/1.48  --inst_learning_loop_flag               true
% 7.19/1.48  --inst_learning_start                   3000
% 7.19/1.48  --inst_learning_factor                  2
% 7.19/1.48  --inst_start_prop_sim_after_learn       3
% 7.19/1.48  --inst_sel_renew                        solver
% 7.19/1.48  --inst_lit_activity_flag                true
% 7.19/1.48  --inst_restr_to_given                   false
% 7.19/1.48  --inst_activity_threshold               500
% 7.19/1.48  --inst_out_proof                        true
% 7.19/1.48  
% 7.19/1.48  ------ Resolution Options
% 7.19/1.48  
% 7.19/1.48  --resolution_flag                       true
% 7.19/1.48  --res_lit_sel                           adaptive
% 7.19/1.48  --res_lit_sel_side                      none
% 7.19/1.48  --res_ordering                          kbo
% 7.19/1.48  --res_to_prop_solver                    active
% 7.19/1.48  --res_prop_simpl_new                    false
% 7.19/1.48  --res_prop_simpl_given                  true
% 7.19/1.48  --res_passive_queue_type                priority_queues
% 7.19/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.19/1.48  --res_passive_queues_freq               [15;5]
% 7.19/1.48  --res_forward_subs                      full
% 7.19/1.48  --res_backward_subs                     full
% 7.19/1.48  --res_forward_subs_resolution           true
% 7.19/1.48  --res_backward_subs_resolution          true
% 7.19/1.48  --res_orphan_elimination                true
% 7.19/1.48  --res_time_limit                        2.
% 7.19/1.48  --res_out_proof                         true
% 7.19/1.48  
% 7.19/1.48  ------ Superposition Options
% 7.19/1.48  
% 7.19/1.48  --superposition_flag                    true
% 7.19/1.48  --sup_passive_queue_type                priority_queues
% 7.19/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.19/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.19/1.48  --demod_completeness_check              fast
% 7.19/1.48  --demod_use_ground                      true
% 7.19/1.48  --sup_to_prop_solver                    passive
% 7.19/1.48  --sup_prop_simpl_new                    true
% 7.19/1.48  --sup_prop_simpl_given                  true
% 7.19/1.48  --sup_fun_splitting                     true
% 7.19/1.48  --sup_smt_interval                      50000
% 7.19/1.48  
% 7.19/1.48  ------ Superposition Simplification Setup
% 7.19/1.48  
% 7.19/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.19/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.19/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.19/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.19/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.19/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.19/1.48  --sup_immed_triv                        [TrivRules]
% 7.19/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.19/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.19/1.48  --sup_immed_bw_main                     []
% 7.19/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.19/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.19/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.19/1.48  --sup_input_bw                          []
% 7.19/1.48  
% 7.19/1.48  ------ Combination Options
% 7.19/1.48  
% 7.19/1.48  --comb_res_mult                         3
% 7.19/1.48  --comb_sup_mult                         2
% 7.19/1.48  --comb_inst_mult                        10
% 7.19/1.48  
% 7.19/1.48  ------ Debug Options
% 7.19/1.48  
% 7.19/1.48  --dbg_backtrace                         false
% 7.19/1.48  --dbg_dump_prop_clauses                 false
% 7.19/1.48  --dbg_dump_prop_clauses_file            -
% 7.19/1.48  --dbg_out_stat                          false
% 7.19/1.48  ------ Parsing...
% 7.19/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.19/1.48  
% 7.19/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.19/1.48  
% 7.19/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.19/1.48  
% 7.19/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.19/1.48  ------ Proving...
% 7.19/1.48  ------ Problem Properties 
% 7.19/1.48  
% 7.19/1.48  
% 7.19/1.48  clauses                                 30
% 7.19/1.48  conjectures                             13
% 7.19/1.48  EPR                                     8
% 7.19/1.48  Horn                                    23
% 7.19/1.48  unary                                   13
% 7.19/1.48  binary                                  4
% 7.19/1.48  lits                                    128
% 7.19/1.48  lits eq                                 21
% 7.19/1.48  fd_pure                                 0
% 7.19/1.48  fd_pseudo                               0
% 7.19/1.48  fd_cond                                 0
% 7.19/1.48  fd_pseudo_cond                          1
% 7.19/1.48  AC symbols                              0
% 7.19/1.48  
% 7.19/1.48  ------ Schedule dynamic 5 is on 
% 7.19/1.48  
% 7.19/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.19/1.48  
% 7.19/1.48  
% 7.19/1.48  ------ 
% 7.19/1.48  Current options:
% 7.19/1.48  ------ 
% 7.19/1.48  
% 7.19/1.48  ------ Input Options
% 7.19/1.48  
% 7.19/1.48  --out_options                           all
% 7.19/1.48  --tptp_safe_out                         true
% 7.19/1.48  --problem_path                          ""
% 7.19/1.48  --include_path                          ""
% 7.19/1.48  --clausifier                            res/vclausify_rel
% 7.19/1.48  --clausifier_options                    ""
% 7.19/1.48  --stdin                                 false
% 7.19/1.48  --stats_out                             all
% 7.19/1.48  
% 7.19/1.48  ------ General Options
% 7.19/1.48  
% 7.19/1.48  --fof                                   false
% 7.19/1.48  --time_out_real                         305.
% 7.19/1.48  --time_out_virtual                      -1.
% 7.19/1.48  --symbol_type_check                     false
% 7.19/1.48  --clausify_out                          false
% 7.19/1.48  --sig_cnt_out                           false
% 7.19/1.48  --trig_cnt_out                          false
% 7.19/1.48  --trig_cnt_out_tolerance                1.
% 7.19/1.48  --trig_cnt_out_sk_spl                   false
% 7.19/1.48  --abstr_cl_out                          false
% 7.19/1.48  
% 7.19/1.48  ------ Global Options
% 7.19/1.48  
% 7.19/1.48  --schedule                              default
% 7.19/1.48  --add_important_lit                     false
% 7.19/1.48  --prop_solver_per_cl                    1000
% 7.19/1.48  --min_unsat_core                        false
% 7.19/1.48  --soft_assumptions                      false
% 7.19/1.48  --soft_lemma_size                       3
% 7.19/1.48  --prop_impl_unit_size                   0
% 7.19/1.48  --prop_impl_unit                        []
% 7.19/1.48  --share_sel_clauses                     true
% 7.19/1.48  --reset_solvers                         false
% 7.19/1.48  --bc_imp_inh                            [conj_cone]
% 7.19/1.48  --conj_cone_tolerance                   3.
% 7.19/1.48  --extra_neg_conj                        none
% 7.19/1.48  --large_theory_mode                     true
% 7.19/1.48  --prolific_symb_bound                   200
% 7.19/1.48  --lt_threshold                          2000
% 7.19/1.48  --clause_weak_htbl                      true
% 7.19/1.48  --gc_record_bc_elim                     false
% 7.19/1.48  
% 7.19/1.48  ------ Preprocessing Options
% 7.19/1.48  
% 7.19/1.48  --preprocessing_flag                    true
% 7.19/1.48  --time_out_prep_mult                    0.1
% 7.19/1.48  --splitting_mode                        input
% 7.19/1.48  --splitting_grd                         true
% 7.19/1.48  --splitting_cvd                         false
% 7.19/1.48  --splitting_cvd_svl                     false
% 7.19/1.48  --splitting_nvd                         32
% 7.19/1.48  --sub_typing                            true
% 7.19/1.48  --prep_gs_sim                           true
% 7.19/1.48  --prep_unflatten                        true
% 7.19/1.48  --prep_res_sim                          true
% 7.19/1.48  --prep_upred                            true
% 7.19/1.48  --prep_sem_filter                       exhaustive
% 7.19/1.48  --prep_sem_filter_out                   false
% 7.19/1.48  --pred_elim                             true
% 7.19/1.48  --res_sim_input                         true
% 7.19/1.48  --eq_ax_congr_red                       true
% 7.19/1.48  --pure_diseq_elim                       true
% 7.19/1.48  --brand_transform                       false
% 7.19/1.48  --non_eq_to_eq                          false
% 7.19/1.48  --prep_def_merge                        true
% 7.19/1.48  --prep_def_merge_prop_impl              false
% 7.19/1.48  --prep_def_merge_mbd                    true
% 7.19/1.48  --prep_def_merge_tr_red                 false
% 7.19/1.48  --prep_def_merge_tr_cl                  false
% 7.19/1.48  --smt_preprocessing                     true
% 7.19/1.48  --smt_ac_axioms                         fast
% 7.19/1.48  --preprocessed_out                      false
% 7.19/1.48  --preprocessed_stats                    false
% 7.19/1.48  
% 7.19/1.48  ------ Abstraction refinement Options
% 7.19/1.48  
% 7.19/1.48  --abstr_ref                             []
% 7.19/1.48  --abstr_ref_prep                        false
% 7.19/1.48  --abstr_ref_until_sat                   false
% 7.19/1.48  --abstr_ref_sig_restrict                funpre
% 7.19/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.19/1.48  --abstr_ref_under                       []
% 7.19/1.48  
% 7.19/1.48  ------ SAT Options
% 7.19/1.48  
% 7.19/1.48  --sat_mode                              false
% 7.19/1.48  --sat_fm_restart_options                ""
% 7.19/1.48  --sat_gr_def                            false
% 7.19/1.48  --sat_epr_types                         true
% 7.19/1.48  --sat_non_cyclic_types                  false
% 7.19/1.48  --sat_finite_models                     false
% 7.19/1.48  --sat_fm_lemmas                         false
% 7.19/1.48  --sat_fm_prep                           false
% 7.19/1.48  --sat_fm_uc_incr                        true
% 7.19/1.48  --sat_out_model                         small
% 7.19/1.48  --sat_out_clauses                       false
% 7.19/1.48  
% 7.19/1.48  ------ QBF Options
% 7.19/1.48  
% 7.19/1.48  --qbf_mode                              false
% 7.19/1.48  --qbf_elim_univ                         false
% 7.19/1.48  --qbf_dom_inst                          none
% 7.19/1.48  --qbf_dom_pre_inst                      false
% 7.19/1.48  --qbf_sk_in                             false
% 7.19/1.48  --qbf_pred_elim                         true
% 7.19/1.48  --qbf_split                             512
% 7.19/1.48  
% 7.19/1.48  ------ BMC1 Options
% 7.19/1.48  
% 7.19/1.48  --bmc1_incremental                      false
% 7.19/1.48  --bmc1_axioms                           reachable_all
% 7.19/1.48  --bmc1_min_bound                        0
% 7.19/1.48  --bmc1_max_bound                        -1
% 7.19/1.48  --bmc1_max_bound_default                -1
% 7.19/1.48  --bmc1_symbol_reachability              true
% 7.19/1.48  --bmc1_property_lemmas                  false
% 7.19/1.48  --bmc1_k_induction                      false
% 7.19/1.48  --bmc1_non_equiv_states                 false
% 7.19/1.48  --bmc1_deadlock                         false
% 7.19/1.48  --bmc1_ucm                              false
% 7.19/1.48  --bmc1_add_unsat_core                   none
% 7.19/1.48  --bmc1_unsat_core_children              false
% 7.19/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.19/1.48  --bmc1_out_stat                         full
% 7.19/1.48  --bmc1_ground_init                      false
% 7.19/1.48  --bmc1_pre_inst_next_state              false
% 7.19/1.48  --bmc1_pre_inst_state                   false
% 7.19/1.48  --bmc1_pre_inst_reach_state             false
% 7.19/1.48  --bmc1_out_unsat_core                   false
% 7.19/1.48  --bmc1_aig_witness_out                  false
% 7.19/1.48  --bmc1_verbose                          false
% 7.19/1.48  --bmc1_dump_clauses_tptp                false
% 7.19/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.19/1.48  --bmc1_dump_file                        -
% 7.19/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.19/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.19/1.48  --bmc1_ucm_extend_mode                  1
% 7.19/1.48  --bmc1_ucm_init_mode                    2
% 7.19/1.48  --bmc1_ucm_cone_mode                    none
% 7.19/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.19/1.48  --bmc1_ucm_relax_model                  4
% 7.19/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.19/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.19/1.48  --bmc1_ucm_layered_model                none
% 7.19/1.48  --bmc1_ucm_max_lemma_size               10
% 7.19/1.48  
% 7.19/1.48  ------ AIG Options
% 7.19/1.48  
% 7.19/1.48  --aig_mode                              false
% 7.19/1.48  
% 7.19/1.48  ------ Instantiation Options
% 7.19/1.48  
% 7.19/1.48  --instantiation_flag                    true
% 7.19/1.48  --inst_sos_flag                         true
% 7.19/1.48  --inst_sos_phase                        true
% 7.19/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.19/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.19/1.48  --inst_lit_sel_side                     none
% 7.19/1.48  --inst_solver_per_active                1400
% 7.19/1.48  --inst_solver_calls_frac                1.
% 7.19/1.48  --inst_passive_queue_type               priority_queues
% 7.19/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.19/1.48  --inst_passive_queues_freq              [25;2]
% 7.19/1.48  --inst_dismatching                      true
% 7.19/1.48  --inst_eager_unprocessed_to_passive     true
% 7.19/1.48  --inst_prop_sim_given                   true
% 7.19/1.48  --inst_prop_sim_new                     false
% 7.19/1.48  --inst_subs_new                         false
% 7.19/1.48  --inst_eq_res_simp                      false
% 7.19/1.48  --inst_subs_given                       false
% 7.19/1.48  --inst_orphan_elimination               true
% 7.19/1.48  --inst_learning_loop_flag               true
% 7.19/1.48  --inst_learning_start                   3000
% 7.19/1.48  --inst_learning_factor                  2
% 7.19/1.48  --inst_start_prop_sim_after_learn       3
% 7.19/1.48  --inst_sel_renew                        solver
% 7.19/1.48  --inst_lit_activity_flag                true
% 7.19/1.48  --inst_restr_to_given                   false
% 7.19/1.48  --inst_activity_threshold               500
% 7.19/1.48  --inst_out_proof                        true
% 7.19/1.48  
% 7.19/1.48  ------ Resolution Options
% 7.19/1.48  
% 7.19/1.48  --resolution_flag                       false
% 7.19/1.48  --res_lit_sel                           adaptive
% 7.19/1.48  --res_lit_sel_side                      none
% 7.19/1.48  --res_ordering                          kbo
% 7.19/1.48  --res_to_prop_solver                    active
% 7.19/1.48  --res_prop_simpl_new                    false
% 7.19/1.48  --res_prop_simpl_given                  true
% 7.19/1.48  --res_passive_queue_type                priority_queues
% 7.19/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.19/1.48  --res_passive_queues_freq               [15;5]
% 7.19/1.48  --res_forward_subs                      full
% 7.19/1.48  --res_backward_subs                     full
% 7.19/1.48  --res_forward_subs_resolution           true
% 7.19/1.48  --res_backward_subs_resolution          true
% 7.19/1.48  --res_orphan_elimination                true
% 7.19/1.48  --res_time_limit                        2.
% 7.19/1.48  --res_out_proof                         true
% 7.19/1.48  
% 7.19/1.48  ------ Superposition Options
% 7.19/1.48  
% 7.19/1.48  --superposition_flag                    true
% 7.19/1.48  --sup_passive_queue_type                priority_queues
% 7.19/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.19/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.19/1.48  --demod_completeness_check              fast
% 7.19/1.48  --demod_use_ground                      true
% 7.19/1.48  --sup_to_prop_solver                    passive
% 7.19/1.48  --sup_prop_simpl_new                    true
% 7.19/1.48  --sup_prop_simpl_given                  true
% 7.19/1.48  --sup_fun_splitting                     true
% 7.19/1.48  --sup_smt_interval                      50000
% 7.19/1.48  
% 7.19/1.48  ------ Superposition Simplification Setup
% 7.19/1.48  
% 7.19/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.19/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.19/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.19/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.19/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.19/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.19/1.48  --sup_immed_triv                        [TrivRules]
% 7.19/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.19/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.19/1.48  --sup_immed_bw_main                     []
% 7.19/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.19/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.19/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.19/1.48  --sup_input_bw                          []
% 7.19/1.48  
% 7.19/1.48  ------ Combination Options
% 7.19/1.48  
% 7.19/1.48  --comb_res_mult                         3
% 7.19/1.48  --comb_sup_mult                         2
% 7.19/1.48  --comb_inst_mult                        10
% 7.19/1.48  
% 7.19/1.48  ------ Debug Options
% 7.19/1.48  
% 7.19/1.48  --dbg_backtrace                         false
% 7.19/1.48  --dbg_dump_prop_clauses                 false
% 7.19/1.48  --dbg_dump_prop_clauses_file            -
% 7.19/1.48  --dbg_out_stat                          false
% 7.19/1.48  
% 7.19/1.48  
% 7.19/1.48  
% 7.19/1.48  
% 7.19/1.48  ------ Proving...
% 7.19/1.48  
% 7.19/1.48  
% 7.19/1.48  % SZS status Theorem for theBenchmark.p
% 7.19/1.48  
% 7.19/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.19/1.48  
% 7.19/1.48  fof(f16,conjecture,(
% 7.19/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f17,negated_conjecture,(
% 7.19/1.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.19/1.48    inference(negated_conjecture,[],[f16])).
% 7.19/1.48  
% 7.19/1.48  fof(f39,plain,(
% 7.19/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.19/1.48    inference(ennf_transformation,[],[f17])).
% 7.19/1.48  
% 7.19/1.48  fof(f40,plain,(
% 7.19/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.19/1.48    inference(flattening,[],[f39])).
% 7.19/1.48  
% 7.19/1.48  fof(f51,plain,(
% 7.19/1.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.19/1.48    introduced(choice_axiom,[])).
% 7.19/1.48  
% 7.19/1.48  fof(f50,plain,(
% 7.19/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.19/1.48    introduced(choice_axiom,[])).
% 7.19/1.48  
% 7.19/1.48  fof(f49,plain,(
% 7.19/1.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.19/1.48    introduced(choice_axiom,[])).
% 7.19/1.48  
% 7.19/1.48  fof(f48,plain,(
% 7.19/1.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.19/1.48    introduced(choice_axiom,[])).
% 7.19/1.48  
% 7.19/1.48  fof(f47,plain,(
% 7.19/1.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.19/1.48    introduced(choice_axiom,[])).
% 7.19/1.48  
% 7.19/1.48  fof(f46,plain,(
% 7.19/1.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.19/1.48    introduced(choice_axiom,[])).
% 7.19/1.48  
% 7.19/1.48  fof(f52,plain,(
% 7.19/1.48    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.19/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f40,f51,f50,f49,f48,f47,f46])).
% 7.19/1.48  
% 7.19/1.48  fof(f81,plain,(
% 7.19/1.48    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f2,axiom,(
% 7.19/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f19,plain,(
% 7.19/1.48    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.19/1.48    inference(ennf_transformation,[],[f2])).
% 7.19/1.48  
% 7.19/1.48  fof(f55,plain,(
% 7.19/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.19/1.48    inference(cnf_transformation,[],[f19])).
% 7.19/1.48  
% 7.19/1.48  fof(f4,axiom,(
% 7.19/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f57,plain,(
% 7.19/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.19/1.48    inference(cnf_transformation,[],[f4])).
% 7.19/1.48  
% 7.19/1.48  fof(f92,plain,(
% 7.19/1.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.19/1.48    inference(definition_unfolding,[],[f55,f57])).
% 7.19/1.48  
% 7.19/1.48  fof(f85,plain,(
% 7.19/1.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f13,axiom,(
% 7.19/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f33,plain,(
% 7.19/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.19/1.48    inference(ennf_transformation,[],[f13])).
% 7.19/1.48  
% 7.19/1.48  fof(f34,plain,(
% 7.19/1.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.19/1.48    inference(flattening,[],[f33])).
% 7.19/1.48  
% 7.19/1.48  fof(f69,plain,(
% 7.19/1.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f34])).
% 7.19/1.48  
% 7.19/1.48  fof(f83,plain,(
% 7.19/1.48    v1_funct_1(sK4)),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f88,plain,(
% 7.19/1.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f86,plain,(
% 7.19/1.48    v1_funct_1(sK5)),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f14,axiom,(
% 7.19/1.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f35,plain,(
% 7.19/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.19/1.48    inference(ennf_transformation,[],[f14])).
% 7.19/1.48  
% 7.19/1.48  fof(f36,plain,(
% 7.19/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.19/1.48    inference(flattening,[],[f35])).
% 7.19/1.48  
% 7.19/1.48  fof(f44,plain,(
% 7.19/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.19/1.48    inference(nnf_transformation,[],[f36])).
% 7.19/1.48  
% 7.19/1.48  fof(f45,plain,(
% 7.19/1.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.19/1.48    inference(flattening,[],[f44])).
% 7.19/1.48  
% 7.19/1.48  fof(f71,plain,(
% 7.19/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f45])).
% 7.19/1.48  
% 7.19/1.48  fof(f97,plain,(
% 7.19/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.19/1.48    inference(equality_resolution,[],[f71])).
% 7.19/1.48  
% 7.19/1.48  fof(f15,axiom,(
% 7.19/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f37,plain,(
% 7.19/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.19/1.48    inference(ennf_transformation,[],[f15])).
% 7.19/1.48  
% 7.19/1.48  fof(f38,plain,(
% 7.19/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.19/1.48    inference(flattening,[],[f37])).
% 7.19/1.48  
% 7.19/1.48  fof(f73,plain,(
% 7.19/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f38])).
% 7.19/1.48  
% 7.19/1.48  fof(f74,plain,(
% 7.19/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f38])).
% 7.19/1.48  
% 7.19/1.48  fof(f75,plain,(
% 7.19/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f38])).
% 7.19/1.48  
% 7.19/1.48  fof(f77,plain,(
% 7.19/1.48    ~v1_xboole_0(sK1)),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f80,plain,(
% 7.19/1.48    ~v1_xboole_0(sK3)),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f87,plain,(
% 7.19/1.48    v1_funct_2(sK5,sK3,sK1)),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f78,plain,(
% 7.19/1.48    ~v1_xboole_0(sK2)),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f84,plain,(
% 7.19/1.48    v1_funct_2(sK4,sK2,sK1)),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f3,axiom,(
% 7.19/1.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f20,plain,(
% 7.19/1.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 7.19/1.48    inference(ennf_transformation,[],[f3])).
% 7.19/1.48  
% 7.19/1.48  fof(f56,plain,(
% 7.19/1.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f20])).
% 7.19/1.48  
% 7.19/1.48  fof(f1,axiom,(
% 7.19/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f41,plain,(
% 7.19/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.19/1.48    inference(nnf_transformation,[],[f1])).
% 7.19/1.48  
% 7.19/1.48  fof(f53,plain,(
% 7.19/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f41])).
% 7.19/1.48  
% 7.19/1.48  fof(f91,plain,(
% 7.19/1.48    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 7.19/1.48    inference(definition_unfolding,[],[f53,f57])).
% 7.19/1.48  
% 7.19/1.48  fof(f8,axiom,(
% 7.19/1.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f25,plain,(
% 7.19/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.19/1.48    inference(ennf_transformation,[],[f8])).
% 7.19/1.48  
% 7.19/1.48  fof(f26,plain,(
% 7.19/1.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.19/1.48    inference(flattening,[],[f25])).
% 7.19/1.48  
% 7.19/1.48  fof(f42,plain,(
% 7.19/1.48    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.19/1.48    inference(nnf_transformation,[],[f26])).
% 7.19/1.48  
% 7.19/1.48  fof(f61,plain,(
% 7.19/1.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f42])).
% 7.19/1.48  
% 7.19/1.48  fof(f82,plain,(
% 7.19/1.48    r1_subset_1(sK2,sK3)),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f9,axiom,(
% 7.19/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f27,plain,(
% 7.19/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.19/1.48    inference(ennf_transformation,[],[f9])).
% 7.19/1.48  
% 7.19/1.48  fof(f63,plain,(
% 7.19/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.19/1.48    inference(cnf_transformation,[],[f27])).
% 7.19/1.48  
% 7.19/1.48  fof(f5,axiom,(
% 7.19/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f21,plain,(
% 7.19/1.48    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.19/1.48    inference(ennf_transformation,[],[f5])).
% 7.19/1.48  
% 7.19/1.48  fof(f58,plain,(
% 7.19/1.48    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f21])).
% 7.19/1.48  
% 7.19/1.48  fof(f93,plain,(
% 7.19/1.48    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_tarski(X0,X1))) | ~v1_relat_1(X2)) )),
% 7.19/1.48    inference(definition_unfolding,[],[f58,f57])).
% 7.19/1.48  
% 7.19/1.48  fof(f7,axiom,(
% 7.19/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.19/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.19/1.48  
% 7.19/1.48  fof(f23,plain,(
% 7.19/1.48    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.19/1.48    inference(ennf_transformation,[],[f7])).
% 7.19/1.48  
% 7.19/1.48  fof(f24,plain,(
% 7.19/1.48    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 7.19/1.48    inference(flattening,[],[f23])).
% 7.19/1.48  
% 7.19/1.48  fof(f60,plain,(
% 7.19/1.48    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f24])).
% 7.19/1.48  
% 7.19/1.48  fof(f79,plain,(
% 7.19/1.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  fof(f70,plain,(
% 7.19/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.19/1.48    inference(cnf_transformation,[],[f45])).
% 7.19/1.48  
% 7.19/1.48  fof(f98,plain,(
% 7.19/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.19/1.48    inference(equality_resolution,[],[f70])).
% 7.19/1.48  
% 7.19/1.48  fof(f89,plain,(
% 7.19/1.48    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.19/1.48    inference(cnf_transformation,[],[f52])).
% 7.19/1.48  
% 7.19/1.48  cnf(c_30,negated_conjecture,
% 7.19/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.19/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1023,negated_conjecture,
% 7.19/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_30]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1544,plain,
% 7.19/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1023]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_2,plain,
% 7.19/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.19/1.48      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 7.19/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1039,plain,
% 7.19/1.48      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.19/1.48      | k9_subset_1(X1_54,X2_54,X0_54) = k1_setfam_1(k2_tarski(X2_54,X0_54)) ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_2]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1529,plain,
% 7.19/1.48      ( k9_subset_1(X0_54,X1_54,X2_54) = k1_setfam_1(k2_tarski(X1_54,X2_54))
% 7.19/1.48      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1039]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_2624,plain,
% 7.19/1.48      ( k9_subset_1(sK0,X0_54,sK3) = k1_setfam_1(k2_tarski(X0_54,sK3)) ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_1544,c_1529]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_26,negated_conjecture,
% 7.19/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.19/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1026,negated_conjecture,
% 7.19/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_26]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1541,plain,
% 7.19/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1026]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_15,plain,
% 7.19/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.48      | ~ v1_funct_1(X0)
% 7.19/1.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.19/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1035,plain,
% 7.19/1.48      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.19/1.48      | ~ v1_funct_1(X0_54)
% 7.19/1.48      | k2_partfun1(X1_54,X2_54,X0_54,X3_54) = k7_relat_1(X0_54,X3_54) ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_15]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1533,plain,
% 7.19/1.48      ( k2_partfun1(X0_54,X1_54,X2_54,X3_54) = k7_relat_1(X2_54,X3_54)
% 7.19/1.48      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.19/1.48      | v1_funct_1(X2_54) != iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1035]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_2812,plain,
% 7.19/1.48      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54)
% 7.19/1.48      | v1_funct_1(sK4) != iProver_top ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_1541,c_1533]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_28,negated_conjecture,
% 7.19/1.48      ( v1_funct_1(sK4) ),
% 7.19/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_43,plain,
% 7.19/1.48      ( v1_funct_1(sK4) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_3429,plain,
% 7.19/1.48      ( k2_partfun1(sK2,sK1,sK4,X0_54) = k7_relat_1(sK4,X0_54) ),
% 7.19/1.48      inference(global_propositional_subsumption,
% 7.19/1.48                [status(thm)],
% 7.19/1.48                [c_2812,c_43]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_23,negated_conjecture,
% 7.19/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.19/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1029,negated_conjecture,
% 7.19/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_23]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1538,plain,
% 7.19/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1029]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_2811,plain,
% 7.19/1.48      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54)
% 7.19/1.48      | v1_funct_1(sK5) != iProver_top ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_1538,c_1533]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_25,negated_conjecture,
% 7.19/1.48      ( v1_funct_1(sK5) ),
% 7.19/1.48      inference(cnf_transformation,[],[f86]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_46,plain,
% 7.19/1.48      ( v1_funct_1(sK5) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_3425,plain,
% 7.19/1.48      ( k2_partfun1(sK3,sK1,sK5,X0_54) = k7_relat_1(sK5,X0_54) ),
% 7.19/1.48      inference(global_propositional_subsumption,
% 7.19/1.48                [status(thm)],
% 7.19/1.48                [c_2811,c_46]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_17,plain,
% 7.19/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.19/1.48      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.19/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.19/1.48      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.19/1.48      | ~ v1_funct_1(X0)
% 7.19/1.48      | ~ v1_funct_1(X3)
% 7.19/1.48      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.19/1.48      | v1_xboole_0(X5)
% 7.19/1.48      | v1_xboole_0(X2)
% 7.19/1.48      | v1_xboole_0(X4)
% 7.19/1.48      | v1_xboole_0(X1)
% 7.19/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.19/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.19/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_21,plain,
% 7.19/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.19/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.19/1.48      | ~ v1_funct_1(X0)
% 7.19/1.48      | ~ v1_funct_1(X3)
% 7.19/1.48      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.19/1.48      | v1_xboole_0(X5)
% 7.19/1.48      | v1_xboole_0(X2)
% 7.19/1.48      | v1_xboole_0(X4)
% 7.19/1.48      | v1_xboole_0(X1) ),
% 7.19/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_20,plain,
% 7.19/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.19/1.48      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.19/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.19/1.48      | ~ v1_funct_1(X0)
% 7.19/1.48      | ~ v1_funct_1(X3)
% 7.19/1.48      | v1_xboole_0(X5)
% 7.19/1.48      | v1_xboole_0(X2)
% 7.19/1.48      | v1_xboole_0(X4)
% 7.19/1.48      | v1_xboole_0(X1) ),
% 7.19/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_19,plain,
% 7.19/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.19/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.19/1.48      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.19/1.48      | ~ v1_funct_1(X0)
% 7.19/1.48      | ~ v1_funct_1(X3)
% 7.19/1.48      | v1_xboole_0(X5)
% 7.19/1.48      | v1_xboole_0(X2)
% 7.19/1.48      | v1_xboole_0(X4)
% 7.19/1.48      | v1_xboole_0(X1) ),
% 7.19/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_203,plain,
% 7.19/1.48      ( ~ v1_funct_1(X3)
% 7.19/1.48      | ~ v1_funct_1(X0)
% 7.19/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.19/1.48      | ~ v1_funct_2(X0,X1,X2)
% 7.19/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.19/1.48      | v1_xboole_0(X5)
% 7.19/1.48      | v1_xboole_0(X2)
% 7.19/1.48      | v1_xboole_0(X4)
% 7.19/1.48      | v1_xboole_0(X1)
% 7.19/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.19/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.19/1.48      inference(global_propositional_subsumption,
% 7.19/1.48                [status(thm)],
% 7.19/1.48                [c_17,c_21,c_20,c_19]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_204,plain,
% 7.19/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.48      | ~ v1_funct_2(X3,X4,X2)
% 7.19/1.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.19/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.19/1.48      | ~ v1_funct_1(X0)
% 7.19/1.48      | ~ v1_funct_1(X3)
% 7.19/1.48      | v1_xboole_0(X1)
% 7.19/1.48      | v1_xboole_0(X2)
% 7.19/1.48      | v1_xboole_0(X4)
% 7.19/1.48      | v1_xboole_0(X5)
% 7.19/1.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.19/1.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.19/1.48      inference(renaming,[status(thm)],[c_203]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1016,plain,
% 7.19/1.48      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.19/1.48      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.19/1.48      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.19/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.19/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.19/1.48      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.19/1.48      | ~ v1_funct_1(X0_54)
% 7.19/1.48      | ~ v1_funct_1(X3_54)
% 7.19/1.48      | v1_xboole_0(X2_54)
% 7.19/1.48      | v1_xboole_0(X1_54)
% 7.19/1.48      | v1_xboole_0(X4_54)
% 7.19/1.48      | v1_xboole_0(X5_54)
% 7.19/1.48      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.19/1.48      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X1_54) = X0_54 ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_204]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1551,plain,
% 7.19/1.48      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.19/1.48      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X0_54) = X2_54
% 7.19/1.48      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.19/1.48      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.19/1.48      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.19/1.48      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.19/1.48      | v1_funct_1(X2_54) != iProver_top
% 7.19/1.48      | v1_funct_1(X5_54) != iProver_top
% 7.19/1.48      | v1_xboole_0(X3_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X1_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X4_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X0_54) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1016]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_5590,plain,
% 7.19/1.48      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.19/1.48      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.19/1.48      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.19/1.48      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.19/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.19/1.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.19/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.48      | v1_funct_1(X1_54) != iProver_top
% 7.19/1.48      | v1_funct_1(sK5) != iProver_top
% 7.19/1.48      | v1_xboole_0(X0_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X2_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(sK1) = iProver_top
% 7.19/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_3425,c_1551]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_34,negated_conjecture,
% 7.19/1.48      ( ~ v1_xboole_0(sK1) ),
% 7.19/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_37,plain,
% 7.19/1.48      ( v1_xboole_0(sK1) != iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_31,negated_conjecture,
% 7.19/1.48      ( ~ v1_xboole_0(sK3) ),
% 7.19/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_40,plain,
% 7.19/1.48      ( v1_xboole_0(sK3) != iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_24,negated_conjecture,
% 7.19/1.48      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.19/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_47,plain,
% 7.19/1.48      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_48,plain,
% 7.19/1.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_10791,plain,
% 7.19/1.48      ( v1_funct_1(X1_54) != iProver_top
% 7.19/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.48      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.19/1.48      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.19/1.48      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.19/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.19/1.48      | v1_xboole_0(X0_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X2_54) = iProver_top ),
% 7.19/1.48      inference(global_propositional_subsumption,
% 7.19/1.48                [status(thm)],
% 7.19/1.48                [c_5590,c_37,c_40,c_46,c_47,c_48]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_10792,plain,
% 7.19/1.48      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.19/1.48      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),sK3) = sK5
% 7.19/1.48      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.19/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.19/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.48      | v1_funct_1(X1_54) != iProver_top
% 7.19/1.48      | v1_xboole_0(X2_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X0_54) = iProver_top ),
% 7.19/1.48      inference(renaming,[status(thm)],[c_10791]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_10798,plain,
% 7.19/1.48      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.19/1.48      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.19/1.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.19/1.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.19/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | v1_funct_1(sK4) != iProver_top
% 7.19/1.48      | v1_xboole_0(X0_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(sK2) = iProver_top ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_3429,c_10792]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_33,negated_conjecture,
% 7.19/1.48      ( ~ v1_xboole_0(sK2) ),
% 7.19/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_38,plain,
% 7.19/1.48      ( v1_xboole_0(sK2) != iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_27,negated_conjecture,
% 7.19/1.48      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.19/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_44,plain,
% 7.19/1.48      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_45,plain,
% 7.19/1.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_3,plain,
% 7.19/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.19/1.48      | ~ v1_xboole_0(X1)
% 7.19/1.48      | v1_xboole_0(X0) ),
% 7.19/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1038,plain,
% 7.19/1.48      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 7.19/1.48      | ~ v1_xboole_0(X1_54)
% 7.19/1.48      | v1_xboole_0(X0_54) ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_3]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1719,plain,
% 7.19/1.48      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0_54))
% 7.19/1.48      | ~ v1_xboole_0(X0_54)
% 7.19/1.48      | v1_xboole_0(sK2) ),
% 7.19/1.48      inference(instantiation,[status(thm)],[c_1038]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1720,plain,
% 7.19/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | v1_xboole_0(X0_54) != iProver_top
% 7.19/1.48      | v1_xboole_0(sK2) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1719]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_10860,plain,
% 7.19/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.19/1.48      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5 ),
% 7.19/1.48      inference(global_propositional_subsumption,
% 7.19/1.48                [status(thm)],
% 7.19/1.48                [c_10798,c_38,c_43,c_44,c_45,c_1720]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_10861,plain,
% 7.19/1.48      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.19/1.48      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.19/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.19/1.48      inference(renaming,[status(thm)],[c_10860]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_10866,plain,
% 7.19/1.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.19/1.48      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
% 7.19/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.19/1.48      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_2624,c_10861]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1,plain,
% 7.19/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.19/1.48      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.19/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_265,plain,
% 7.19/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.19/1.48      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 7.19/1.48      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_8,plain,
% 7.19/1.48      ( ~ r1_subset_1(X0,X1)
% 7.19/1.48      | r1_xboole_0(X0,X1)
% 7.19/1.48      | v1_xboole_0(X0)
% 7.19/1.48      | v1_xboole_0(X1) ),
% 7.19/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_29,negated_conjecture,
% 7.19/1.48      ( r1_subset_1(sK2,sK3) ),
% 7.19/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_557,plain,
% 7.19/1.48      ( r1_xboole_0(X0,X1)
% 7.19/1.48      | v1_xboole_0(X0)
% 7.19/1.48      | v1_xboole_0(X1)
% 7.19/1.48      | sK3 != X1
% 7.19/1.48      | sK2 != X0 ),
% 7.19/1.48      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_558,plain,
% 7.19/1.48      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.19/1.48      inference(unflattening,[status(thm)],[c_557]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_560,plain,
% 7.19/1.48      ( r1_xboole_0(sK2,sK3) ),
% 7.19/1.48      inference(global_propositional_subsumption,
% 7.19/1.48                [status(thm)],
% 7.19/1.48                [c_558,c_33,c_31]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_644,plain,
% 7.19/1.48      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 7.19/1.48      | sK3 != X1
% 7.19/1.48      | sK2 != X0 ),
% 7.19/1.48      inference(resolution_lifted,[status(thm)],[c_265,c_560]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_645,plain,
% 7.19/1.48      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.19/1.48      inference(unflattening,[status(thm)],[c_644]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1011,plain,
% 7.19/1.48      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_645]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_9,plain,
% 7.19/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.48      | v1_relat_1(X0) ),
% 7.19/1.48      inference(cnf_transformation,[],[f63]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1036,plain,
% 7.19/1.48      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.19/1.48      | v1_relat_1(X0_54) ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_9]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1532,plain,
% 7.19/1.48      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.19/1.48      | v1_relat_1(X0_54) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1036]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_2421,plain,
% 7.19/1.48      ( v1_relat_1(sK5) = iProver_top ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_1538,c_1532]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_4,plain,
% 7.19/1.48      ( ~ v1_relat_1(X0)
% 7.19/1.48      | k7_relat_1(X0,k1_setfam_1(k2_tarski(X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.19/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1037,plain,
% 7.19/1.48      ( ~ v1_relat_1(X0_54)
% 7.19/1.48      | k7_relat_1(X0_54,k1_setfam_1(k2_tarski(X1_54,X2_54))) = k7_relat_1(k7_relat_1(X0_54,X1_54),X2_54) ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_4]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1531,plain,
% 7.19/1.48      ( k7_relat_1(X0_54,k1_setfam_1(k2_tarski(X1_54,X2_54))) = k7_relat_1(k7_relat_1(X0_54,X1_54),X2_54)
% 7.19/1.48      | v1_relat_1(X0_54) != iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1037]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_2722,plain,
% 7.19/1.48      ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(X0_54,X1_54))) = k7_relat_1(k7_relat_1(sK5,X0_54),X1_54) ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_2421,c_1531]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_3595,plain,
% 7.19/1.48      ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) = k7_relat_1(sK5,k1_xboole_0) ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_1011,c_2722]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_6,plain,
% 7.19/1.48      ( ~ r1_xboole_0(X0,X1)
% 7.19/1.48      | ~ v1_relat_1(X2)
% 7.19/1.48      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 7.19/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_632,plain,
% 7.19/1.48      ( ~ v1_relat_1(X0)
% 7.19/1.48      | k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
% 7.19/1.48      | sK3 != X2
% 7.19/1.48      | sK2 != X1 ),
% 7.19/1.48      inference(resolution_lifted,[status(thm)],[c_6,c_560]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_633,plain,
% 7.19/1.48      ( ~ v1_relat_1(X0)
% 7.19/1.48      | k7_relat_1(k7_relat_1(X0,sK2),sK3) = k1_xboole_0 ),
% 7.19/1.48      inference(unflattening,[status(thm)],[c_632]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1012,plain,
% 7.19/1.48      ( ~ v1_relat_1(X0_54)
% 7.19/1.48      | k7_relat_1(k7_relat_1(X0_54,sK2),sK3) = k1_xboole_0 ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_633]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1555,plain,
% 7.19/1.48      ( k7_relat_1(k7_relat_1(X0_54,sK2),sK3) = k1_xboole_0
% 7.19/1.48      | v1_relat_1(X0_54) != iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1012]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_2426,plain,
% 7.19/1.48      ( k7_relat_1(k7_relat_1(sK5,sK2),sK3) = k1_xboole_0 ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_2421,c_1555]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_3596,plain,
% 7.19/1.48      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.19/1.48      inference(light_normalisation,[status(thm)],[c_3595,c_2426]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_10867,plain,
% 7.19/1.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.19/1.48      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.19/1.48      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.19/1.48      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.48      inference(light_normalisation,
% 7.19/1.48                [status(thm)],
% 7.19/1.48                [c_10866,c_1011,c_3596]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_2422,plain,
% 7.19/1.48      ( v1_relat_1(sK4) = iProver_top ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_1541,c_1532]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_2723,plain,
% 7.19/1.48      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(X0_54,X1_54))) = k7_relat_1(k7_relat_1(sK4,X0_54),X1_54) ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_2422,c_1531]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1031,plain,
% 7.19/1.48      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.19/1.48      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.19/1.48      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.19/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.19/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.19/1.48      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.19/1.48      | ~ v1_funct_1(X0_54)
% 7.19/1.48      | ~ v1_funct_1(X3_54)
% 7.19/1.48      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54))
% 7.19/1.48      | v1_xboole_0(X2_54)
% 7.19/1.48      | v1_xboole_0(X1_54)
% 7.19/1.48      | v1_xboole_0(X4_54)
% 7.19/1.48      | v1_xboole_0(X5_54) ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_21]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1537,plain,
% 7.19/1.48      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.19/1.48      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.19/1.48      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.19/1.48      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.19/1.48      | v1_funct_1(X0_54) != iProver_top
% 7.19/1.48      | v1_funct_1(X3_54) != iProver_top
% 7.19/1.48      | v1_funct_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54)) = iProver_top
% 7.19/1.48      | v1_xboole_0(X5_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X2_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X4_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X1_54) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1031]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1033,plain,
% 7.19/1.48      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.19/1.48      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.19/1.48      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.19/1.48      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.19/1.48      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.19/1.48      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.19/1.48      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54)))
% 7.19/1.48      | ~ v1_funct_1(X0_54)
% 7.19/1.48      | ~ v1_funct_1(X3_54)
% 7.19/1.48      | v1_xboole_0(X2_54)
% 7.19/1.48      | v1_xboole_0(X1_54)
% 7.19/1.48      | v1_xboole_0(X4_54)
% 7.19/1.48      | v1_xboole_0(X5_54) ),
% 7.19/1.48      inference(subtyping,[status(esa)],[c_19]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1535,plain,
% 7.19/1.48      ( v1_funct_2(X0_54,X1_54,X2_54) != iProver_top
% 7.19/1.48      | v1_funct_2(X3_54,X4_54,X2_54) != iProver_top
% 7.19/1.48      | m1_subset_1(X4_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(X5_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54))) != iProver_top
% 7.19/1.48      | m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54))) != iProver_top
% 7.19/1.48      | m1_subset_1(k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_54,X4_54,X1_54),X2_54))) = iProver_top
% 7.19/1.48      | v1_funct_1(X0_54) != iProver_top
% 7.19/1.48      | v1_funct_1(X3_54) != iProver_top
% 7.19/1.48      | v1_xboole_0(X5_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X2_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X4_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X1_54) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1033]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_3581,plain,
% 7.19/1.48      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 7.19/1.48      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 7.19/1.48      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 7.19/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.19/1.48      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 7.19/1.48      | v1_funct_1(X5_54) != iProver_top
% 7.19/1.48      | v1_funct_1(X4_54) != iProver_top
% 7.19/1.48      | v1_funct_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54)) != iProver_top
% 7.19/1.48      | v1_xboole_0(X0_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X3_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X1_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X2_54) = iProver_top ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_1535,c_1533]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_6311,plain,
% 7.19/1.48      ( k2_partfun1(k4_subset_1(X0_54,X1_54,X2_54),X3_54,k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54) = k7_relat_1(k1_tmap_1(X0_54,X3_54,X1_54,X2_54,X4_54,X5_54),X6_54)
% 7.19/1.48      | v1_funct_2(X5_54,X2_54,X3_54) != iProver_top
% 7.19/1.48      | v1_funct_2(X4_54,X1_54,X3_54) != iProver_top
% 7.19/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X2_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X2_54,X3_54))) != iProver_top
% 7.19/1.48      | m1_subset_1(X4_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X3_54))) != iProver_top
% 7.19/1.48      | v1_funct_1(X5_54) != iProver_top
% 7.19/1.48      | v1_funct_1(X4_54) != iProver_top
% 7.19/1.48      | v1_xboole_0(X0_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X3_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X1_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X2_54) = iProver_top ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_1537,c_3581]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_6603,plain,
% 7.19/1.48      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 7.19/1.48      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 7.19/1.48      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.19/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 7.19/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | v1_funct_1(X2_54) != iProver_top
% 7.19/1.48      | v1_funct_1(sK5) != iProver_top
% 7.19/1.48      | v1_xboole_0(X1_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(X0_54) = iProver_top
% 7.19/1.48      | v1_xboole_0(sK1) = iProver_top
% 7.19/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.19/1.48      inference(superposition,[status(thm)],[c_1538,c_6311]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1758,plain,
% 7.19/1.48      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0_54))
% 7.19/1.48      | ~ v1_xboole_0(X0_54)
% 7.19/1.48      | v1_xboole_0(sK3) ),
% 7.19/1.48      inference(instantiation,[status(thm)],[c_1038]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_1759,plain,
% 7.19/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | v1_xboole_0(X0_54) != iProver_top
% 7.19/1.48      | v1_xboole_0(sK3) = iProver_top ),
% 7.19/1.48      inference(predicate_to_equality,[status(thm)],[c_1758]) ).
% 7.19/1.48  
% 7.19/1.48  cnf(c_6616,plain,
% 7.19/1.48      ( v1_xboole_0(X1_54) = iProver_top
% 7.19/1.48      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 7.19/1.48      | k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 7.19/1.48      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 7.19/1.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.48      | v1_funct_1(X2_54) != iProver_top ),
% 7.19/1.48      inference(global_propositional_subsumption,
% 7.19/1.48                [status(thm)],
% 7.19/1.48                [c_6603,c_37,c_40,c_46,c_47,c_1759]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_6617,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(X0_54,X1_54,sK3),sK1,k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,X1_54,sK3,X2_54,sK5),X3_54)
% 7.19/1.49      | v1_funct_2(X2_54,X1_54,sK1) != iProver_top
% 7.19/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,sK1))) != iProver_top
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.49      | v1_funct_1(X2_54) != iProver_top
% 7.19/1.49      | v1_xboole_0(X1_54) = iProver_top ),
% 7.19/1.49      inference(renaming,[status(thm)],[c_6616]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_6623,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
% 7.19/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.49      | v1_funct_1(sK4) != iProver_top
% 7.19/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.19/1.49      inference(superposition,[status(thm)],[c_1541,c_6617]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_6701,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54) = k7_relat_1(k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),X1_54)
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.19/1.49      inference(global_propositional_subsumption,
% 7.19/1.49                [status(thm)],
% 7.19/1.49                [c_6623,c_38,c_43,c_44]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_6707,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54)
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.49      inference(superposition,[status(thm)],[c_1544,c_6701]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_32,negated_conjecture,
% 7.19/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.19/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_39,plain,
% 7.19/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.19/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_6712,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_54) ),
% 7.19/1.49      inference(global_propositional_subsumption,
% 7.19/1.49                [status(thm)],
% 7.19/1.49                [c_6707,c_39]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_10868,plain,
% 7.19/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.19/1.49      | k7_relat_1(k7_relat_1(sK4,sK2),sK3) != k1_xboole_0
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.49      inference(demodulation,
% 7.19/1.49                [status(thm)],
% 7.19/1.49                [c_10867,c_2624,c_2723,c_6712]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_2528,plain,
% 7.19/1.49      ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k1_xboole_0 ),
% 7.19/1.49      inference(superposition,[status(thm)],[c_2422,c_1555]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_10869,plain,
% 7.19/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.19/1.49      | k1_xboole_0 != k1_xboole_0
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.49      inference(light_normalisation,[status(thm)],[c_10868,c_2528]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_10870,plain,
% 7.19/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.49      inference(equality_resolution_simp,[status(thm)],[c_10869]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_18,plain,
% 7.19/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.19/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.19/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.19/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.19/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.19/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.19/1.49      | ~ v1_funct_1(X0)
% 7.19/1.49      | ~ v1_funct_1(X3)
% 7.19/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.19/1.49      | v1_xboole_0(X5)
% 7.19/1.49      | v1_xboole_0(X2)
% 7.19/1.49      | v1_xboole_0(X4)
% 7.19/1.49      | v1_xboole_0(X1)
% 7.19/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.19/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.19/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_196,plain,
% 7.19/1.49      ( ~ v1_funct_1(X3)
% 7.19/1.49      | ~ v1_funct_1(X0)
% 7.19/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.19/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.19/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.19/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.19/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.19/1.49      | v1_xboole_0(X5)
% 7.19/1.49      | v1_xboole_0(X2)
% 7.19/1.49      | v1_xboole_0(X4)
% 7.19/1.49      | v1_xboole_0(X1)
% 7.19/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.19/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.19/1.49      inference(global_propositional_subsumption,
% 7.19/1.49                [status(thm)],
% 7.19/1.49                [c_18,c_21,c_20,c_19]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_197,plain,
% 7.19/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.19/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.19/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.19/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.19/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.19/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.19/1.49      | ~ v1_funct_1(X0)
% 7.19/1.49      | ~ v1_funct_1(X3)
% 7.19/1.49      | v1_xboole_0(X1)
% 7.19/1.49      | v1_xboole_0(X2)
% 7.19/1.49      | v1_xboole_0(X4)
% 7.19/1.49      | v1_xboole_0(X5)
% 7.19/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.19/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.19/1.49      inference(renaming,[status(thm)],[c_196]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_1017,plain,
% 7.19/1.49      ( ~ v1_funct_2(X0_54,X1_54,X2_54)
% 7.19/1.49      | ~ v1_funct_2(X3_54,X4_54,X2_54)
% 7.19/1.49      | ~ m1_subset_1(X4_54,k1_zfmisc_1(X5_54))
% 7.19/1.49      | ~ m1_subset_1(X1_54,k1_zfmisc_1(X5_54))
% 7.19/1.49      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X1_54,X2_54)))
% 7.19/1.49      | ~ m1_subset_1(X3_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X2_54)))
% 7.19/1.49      | ~ v1_funct_1(X0_54)
% 7.19/1.49      | ~ v1_funct_1(X3_54)
% 7.19/1.49      | v1_xboole_0(X2_54)
% 7.19/1.49      | v1_xboole_0(X1_54)
% 7.19/1.49      | v1_xboole_0(X4_54)
% 7.19/1.49      | v1_xboole_0(X5_54)
% 7.19/1.49      | k2_partfun1(X1_54,X2_54,X0_54,k9_subset_1(X5_54,X4_54,X1_54)) != k2_partfun1(X4_54,X2_54,X3_54,k9_subset_1(X5_54,X4_54,X1_54))
% 7.19/1.49      | k2_partfun1(k4_subset_1(X5_54,X4_54,X1_54),X2_54,k1_tmap_1(X5_54,X2_54,X4_54,X1_54,X3_54,X0_54),X4_54) = X3_54 ),
% 7.19/1.49      inference(subtyping,[status(esa)],[c_197]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_1550,plain,
% 7.19/1.49      ( k2_partfun1(X0_54,X1_54,X2_54,k9_subset_1(X3_54,X4_54,X0_54)) != k2_partfun1(X4_54,X1_54,X5_54,k9_subset_1(X3_54,X4_54,X0_54))
% 7.19/1.49      | k2_partfun1(k4_subset_1(X3_54,X4_54,X0_54),X1_54,k1_tmap_1(X3_54,X1_54,X4_54,X0_54,X5_54,X2_54),X4_54) = X5_54
% 7.19/1.49      | v1_funct_2(X2_54,X0_54,X1_54) != iProver_top
% 7.19/1.49      | v1_funct_2(X5_54,X4_54,X1_54) != iProver_top
% 7.19/1.49      | m1_subset_1(X4_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X3_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(X2_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 7.19/1.49      | m1_subset_1(X5_54,k1_zfmisc_1(k2_zfmisc_1(X4_54,X1_54))) != iProver_top
% 7.19/1.49      | v1_funct_1(X2_54) != iProver_top
% 7.19/1.49      | v1_funct_1(X5_54) != iProver_top
% 7.19/1.49      | v1_xboole_0(X3_54) = iProver_top
% 7.19/1.49      | v1_xboole_0(X1_54) = iProver_top
% 7.19/1.49      | v1_xboole_0(X4_54) = iProver_top
% 7.19/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.19/1.49      inference(predicate_to_equality,[status(thm)],[c_1017]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_3828,plain,
% 7.19/1.49      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.19/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.19/1.49      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.19/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.19/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.19/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.19/1.49      | v1_funct_1(sK5) != iProver_top
% 7.19/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.19/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.19/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.19/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.19/1.49      inference(superposition,[status(thm)],[c_3425,c_1550]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_6481,plain,
% 7.19/1.49      ( v1_funct_1(X1_54) != iProver_top
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.49      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.19/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.19/1.49      | k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.19/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.19/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.19/1.49      | v1_xboole_0(X2_54) = iProver_top ),
% 7.19/1.49      inference(global_propositional_subsumption,
% 7.19/1.49                [status(thm)],
% 7.19/1.49                [c_3828,c_37,c_40,c_46,c_47,c_48]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_6482,plain,
% 7.19/1.49      ( k2_partfun1(X0_54,sK1,X1_54,k9_subset_1(X2_54,X0_54,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_54,X0_54,sK3))
% 7.19/1.49      | k2_partfun1(k4_subset_1(X2_54,X0_54,sK3),sK1,k1_tmap_1(X2_54,sK1,X0_54,sK3,X1_54,sK5),X0_54) = X1_54
% 7.19/1.49      | v1_funct_2(X1_54,X0_54,sK1) != iProver_top
% 7.19/1.49      | m1_subset_1(X0_54,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(X1_54,k1_zfmisc_1(k2_zfmisc_1(X0_54,sK1))) != iProver_top
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_54)) != iProver_top
% 7.19/1.49      | v1_funct_1(X1_54) != iProver_top
% 7.19/1.49      | v1_xboole_0(X2_54) = iProver_top
% 7.19/1.49      | v1_xboole_0(X0_54) = iProver_top ),
% 7.19/1.49      inference(renaming,[status(thm)],[c_6481]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_6488,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.19/1.49      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.19/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.19/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.49      | v1_funct_1(sK4) != iProver_top
% 7.19/1.49      | v1_xboole_0(X0_54) = iProver_top
% 7.19/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.19/1.49      inference(superposition,[status(thm)],[c_3429,c_6482]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_8944,plain,
% 7.19/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.49      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.19/1.49      | k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 7.19/1.49      inference(global_propositional_subsumption,
% 7.19/1.49                [status(thm)],
% 7.19/1.49                [c_6488,c_38,c_43,c_44,c_45,c_1720]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_8945,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(X0_54,sK2,sK3),sK1,k1_tmap_1(X0_54,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.19/1.49      | k7_relat_1(sK5,k9_subset_1(X0_54,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_54,sK2,sK3))
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_54)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_54)) != iProver_top ),
% 7.19/1.49      inference(renaming,[status(thm)],[c_8944]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_8950,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.19/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.49      inference(superposition,[status(thm)],[c_2624,c_8945]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_8951,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.19/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.49      inference(light_normalisation,[status(thm)],[c_8950,c_1011,c_3596]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_8952,plain,
% 7.19/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.19/1.49      | k7_relat_1(k7_relat_1(sK4,sK2),sK3) != k1_xboole_0
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.49      inference(demodulation,[status(thm)],[c_8951,c_2624,c_2723,c_6712]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_8953,plain,
% 7.19/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.19/1.49      | k1_xboole_0 != k1_xboole_0
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.49      inference(light_normalisation,[status(thm)],[c_8952,c_2528]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_8954,plain,
% 7.19/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.19/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.19/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.19/1.49      inference(equality_resolution_simp,[status(thm)],[c_8953]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_22,negated_conjecture,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.19/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.19/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.19/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_1030,negated_conjecture,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.19/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.19/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.19/1.49      inference(subtyping,[status(esa)],[c_22]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_2857,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.19/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.19/1.49      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 7.19/1.49      inference(demodulation,[status(thm)],[c_2624,c_1030]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_2858,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.19/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.19/1.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.19/1.49      inference(light_normalisation,[status(thm)],[c_2857,c_1011]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_3609,plain,
% 7.19/1.49      ( k7_relat_1(k7_relat_1(sK4,sK2),sK3) = k7_relat_1(sK4,k1_xboole_0) ),
% 7.19/1.49      inference(superposition,[status(thm)],[c_1011,c_2723]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_3610,plain,
% 7.19/1.49      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.19/1.49      inference(light_normalisation,[status(thm)],[c_3609,c_2528]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_3611,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.19/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.19/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.19/1.49      inference(demodulation,
% 7.19/1.49                [status(thm)],
% 7.19/1.49                [c_2858,c_3425,c_3429,c_3596,c_3610]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_3612,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.19/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.19/1.49      inference(equality_resolution_simp,[status(thm)],[c_3611]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_6715,plain,
% 7.19/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.19/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.19/1.49      inference(demodulation,[status(thm)],[c_6712,c_3612]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_6716,plain,
% 7.19/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.19/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.19/1.49      inference(demodulation,[status(thm)],[c_6715,c_6712]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(c_41,plain,
% 7.19/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.19/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.19/1.49  
% 7.19/1.49  cnf(contradiction,plain,
% 7.19/1.49      ( $false ),
% 7.19/1.49      inference(minisat,[status(thm)],[c_10870,c_8954,c_6716,c_41,c_39]) ).
% 7.19/1.49  
% 7.19/1.49  
% 7.19/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.19/1.49  
% 7.19/1.49  ------                               Statistics
% 7.19/1.49  
% 7.19/1.49  ------ General
% 7.19/1.49  
% 7.19/1.49  abstr_ref_over_cycles:                  0
% 7.19/1.49  abstr_ref_under_cycles:                 0
% 7.19/1.49  gc_basic_clause_elim:                   0
% 7.19/1.49  forced_gc_time:                         0
% 7.19/1.49  parsing_time:                           0.012
% 7.19/1.49  unif_index_cands_time:                  0.
% 7.19/1.49  unif_index_add_time:                    0.
% 7.19/1.49  orderings_time:                         0.
% 7.19/1.49  out_proof_time:                         0.018
% 7.19/1.49  total_time:                             0.718
% 7.19/1.49  num_of_symbols:                         60
% 7.19/1.49  num_of_terms:                           29624
% 7.19/1.49  
% 7.19/1.49  ------ Preprocessing
% 7.19/1.49  
% 7.19/1.49  num_of_splits:                          0
% 7.19/1.49  num_of_split_atoms:                     0
% 7.19/1.49  num_of_reused_defs:                     0
% 7.19/1.49  num_eq_ax_congr_red:                    11
% 7.19/1.49  num_of_sem_filtered_clauses:            1
% 7.19/1.49  num_of_subtypes:                        3
% 7.19/1.49  monotx_restored_types:                  0
% 7.19/1.49  sat_num_of_epr_types:                   0
% 7.19/1.49  sat_num_of_non_cyclic_types:            0
% 7.19/1.49  sat_guarded_non_collapsed_types:        1
% 7.19/1.49  num_pure_diseq_elim:                    0
% 7.19/1.49  simp_replaced_by:                       0
% 7.19/1.49  res_preprocessed:                       160
% 7.19/1.49  prep_upred:                             0
% 7.19/1.49  prep_unflattend:                        15
% 7.19/1.49  smt_new_axioms:                         0
% 7.19/1.49  pred_elim_cands:                        5
% 7.19/1.49  pred_elim:                              4
% 7.19/1.49  pred_elim_cl:                           5
% 7.19/1.49  pred_elim_cycles:                       7
% 7.19/1.49  merged_defs:                            2
% 7.19/1.49  merged_defs_ncl:                        0
% 7.19/1.49  bin_hyper_res:                          2
% 7.19/1.49  prep_cycles:                            4
% 7.19/1.49  pred_elim_time:                         0.008
% 7.19/1.49  splitting_time:                         0.001
% 7.19/1.49  sem_filter_time:                        0.
% 7.19/1.49  monotx_time:                            0.
% 7.19/1.49  subtype_inf_time:                       0.001
% 7.19/1.49  
% 7.19/1.49  ------ Problem properties
% 7.19/1.49  
% 7.19/1.49  clauses:                                30
% 7.19/1.49  conjectures:                            13
% 7.19/1.49  epr:                                    8
% 7.19/1.49  horn:                                   23
% 7.19/1.49  ground:                                 14
% 7.19/1.49  unary:                                  13
% 7.19/1.49  binary:                                 4
% 7.19/1.49  lits:                                   128
% 7.19/1.49  lits_eq:                                21
% 7.19/1.49  fd_pure:                                0
% 7.19/1.49  fd_pseudo:                              0
% 7.19/1.49  fd_cond:                                0
% 7.19/1.49  fd_pseudo_cond:                         1
% 7.19/1.49  ac_symbols:                             0
% 7.19/1.49  
% 7.19/1.49  ------ Propositional Solver
% 7.19/1.49  
% 7.19/1.49  prop_solver_calls:                      30
% 7.19/1.49  prop_fast_solver_calls:                 2891
% 7.19/1.49  smt_solver_calls:                       0
% 7.19/1.49  smt_fast_solver_calls:                  0
% 7.19/1.49  prop_num_of_clauses:                    6147
% 7.19/1.49  prop_preprocess_simplified:             14106
% 7.19/1.49  prop_fo_subsumed:                       216
% 7.19/1.49  prop_solver_time:                       0.
% 7.19/1.49  smt_solver_time:                        0.
% 7.19/1.49  smt_fast_solver_time:                   0.
% 7.19/1.49  prop_fast_solver_time:                  0.
% 7.19/1.49  prop_unsat_core_time:                   0.
% 7.19/1.49  
% 7.19/1.49  ------ QBF
% 7.19/1.49  
% 7.19/1.49  qbf_q_res:                              0
% 7.19/1.49  qbf_num_tautologies:                    0
% 7.19/1.49  qbf_prep_cycles:                        0
% 7.19/1.49  
% 7.19/1.49  ------ BMC1
% 7.19/1.49  
% 7.19/1.49  bmc1_current_bound:                     -1
% 7.19/1.49  bmc1_last_solved_bound:                 -1
% 7.19/1.49  bmc1_unsat_core_size:                   -1
% 7.19/1.49  bmc1_unsat_core_parents_size:           -1
% 7.19/1.49  bmc1_merge_next_fun:                    0
% 7.19/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.19/1.49  
% 7.19/1.49  ------ Instantiation
% 7.19/1.49  
% 7.19/1.49  inst_num_of_clauses:                    1443
% 7.19/1.49  inst_num_in_passive:                    687
% 7.19/1.49  inst_num_in_active:                     593
% 7.19/1.49  inst_num_in_unprocessed:                163
% 7.19/1.49  inst_num_of_loops:                      760
% 7.19/1.49  inst_num_of_learning_restarts:          0
% 7.19/1.49  inst_num_moves_active_passive:          164
% 7.19/1.49  inst_lit_activity:                      0
% 7.19/1.49  inst_lit_activity_moves:                1
% 7.19/1.49  inst_num_tautologies:                   0
% 7.19/1.49  inst_num_prop_implied:                  0
% 7.19/1.49  inst_num_existing_simplified:           0
% 7.19/1.49  inst_num_eq_res_simplified:             0
% 7.19/1.49  inst_num_child_elim:                    0
% 7.19/1.49  inst_num_of_dismatching_blockings:      83
% 7.19/1.49  inst_num_of_non_proper_insts:           1287
% 7.19/1.49  inst_num_of_duplicates:                 0
% 7.19/1.49  inst_inst_num_from_inst_to_res:         0
% 7.19/1.49  inst_dismatching_checking_time:         0.
% 7.19/1.49  
% 7.19/1.49  ------ Resolution
% 7.19/1.49  
% 7.19/1.49  res_num_of_clauses:                     0
% 7.19/1.49  res_num_in_passive:                     0
% 7.19/1.49  res_num_in_active:                      0
% 7.19/1.49  res_num_of_loops:                       164
% 7.19/1.49  res_forward_subset_subsumed:            22
% 7.19/1.49  res_backward_subset_subsumed:           2
% 7.19/1.49  res_forward_subsumed:                   0
% 7.19/1.49  res_backward_subsumed:                  0
% 7.19/1.49  res_forward_subsumption_resolution:     1
% 7.19/1.49  res_backward_subsumption_resolution:    0
% 7.19/1.49  res_clause_to_clause_subsumption:       568
% 7.19/1.49  res_orphan_elimination:                 0
% 7.19/1.49  res_tautology_del:                      17
% 7.19/1.49  res_num_eq_res_simplified:              0
% 7.19/1.49  res_num_sel_changes:                    0
% 7.19/1.49  res_moves_from_active_to_pass:          0
% 7.19/1.49  
% 7.19/1.49  ------ Superposition
% 7.19/1.49  
% 7.19/1.49  sup_time_total:                         0.
% 7.19/1.49  sup_time_generating:                    0.
% 7.19/1.49  sup_time_sim_full:                      0.
% 7.19/1.49  sup_time_sim_immed:                     0.
% 7.19/1.49  
% 7.19/1.49  sup_num_of_clauses:                     231
% 7.19/1.49  sup_num_in_active:                      136
% 7.19/1.49  sup_num_in_passive:                     95
% 7.19/1.49  sup_num_of_loops:                       150
% 7.19/1.49  sup_fw_superposition:                   178
% 7.19/1.49  sup_bw_superposition:                   70
% 7.19/1.49  sup_immediate_simplified:               95
% 7.19/1.49  sup_given_eliminated:                   0
% 7.19/1.49  comparisons_done:                       0
% 7.19/1.49  comparisons_avoided:                    0
% 7.19/1.49  
% 7.19/1.49  ------ Simplifications
% 7.19/1.49  
% 7.19/1.49  
% 7.19/1.49  sim_fw_subset_subsumed:                 4
% 7.19/1.49  sim_bw_subset_subsumed:                 0
% 7.19/1.49  sim_fw_subsumed:                        3
% 7.19/1.49  sim_bw_subsumed:                        10
% 7.19/1.49  sim_fw_subsumption_res:                 0
% 7.19/1.49  sim_bw_subsumption_res:                 0
% 7.19/1.49  sim_tautology_del:                      0
% 7.19/1.49  sim_eq_tautology_del:                   6
% 7.19/1.49  sim_eq_res_simp:                        3
% 7.19/1.49  sim_fw_demodulated:                     68
% 7.19/1.49  sim_bw_demodulated:                     5
% 7.19/1.49  sim_light_normalised:                   34
% 7.19/1.49  sim_joinable_taut:                      0
% 7.19/1.49  sim_joinable_simp:                      0
% 7.19/1.49  sim_ac_normalised:                      0
% 7.19/1.49  sim_smt_subsumption:                    0
% 7.19/1.49  
%------------------------------------------------------------------------------
