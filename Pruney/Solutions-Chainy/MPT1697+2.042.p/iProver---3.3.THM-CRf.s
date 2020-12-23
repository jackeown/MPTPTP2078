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
% DateTime   : Thu Dec  3 12:21:31 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  192 (2115 expanded)
%              Number of clauses        :  108 ( 523 expanded)
%              Number of leaves         :   23 ( 805 expanded)
%              Depth                    :   21
%              Number of atoms          : 1036 (24337 expanded)
%              Number of equality atoms :  359 (5754 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f33,plain,(
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
    inference(flattening,[],[f33])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
          & v1_funct_2(X5,X3,X1)
          & v1_funct_1(X5) )
     => ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7
          | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4
          | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) )
        & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(sK7,X3,X1)
        & v1_funct_1(sK7) ) ) ),
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
            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5
              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6
              | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
            & v1_funct_2(X5,X3,X1)
            & v1_funct_1(X5) )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(sK6,X2,X1)
        & v1_funct_1(sK6) ) ) ),
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
                ( ( k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5
                  | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4
                  | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1)))
                & v1_funct_2(X5,sK5,X1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(X4,X2,X1)
            & v1_funct_1(X4) )
        & r1_subset_1(X2,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK5) ) ) ),
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
                    ( ( k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4
                      | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                    & v1_funct_2(X5,X3,X1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1)))
                & v1_funct_2(X4,sK4,X1)
                & v1_funct_1(X4) )
            & r1_subset_1(sK4,X3)
            & m1_subset_1(X3,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(sK4,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(sK4) ) ) ),
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
                        ( ( k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3)))
                        & v1_funct_2(X5,X3,sK3)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3)))
                    & v1_funct_2(X4,X2,sK3)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(X0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(sK3) ) ) ),
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
                          ( ( k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK2))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK2))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))
    & v1_funct_2(sK7,sK5,sK3)
    & v1_funct_1(sK7)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))
    & v1_funct_2(sK6,sK4,sK3)
    & v1_funct_1(sK6)
    & r1_subset_1(sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(sK2))
    & ~ v1_xboole_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(sK2))
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f34,f48,f47,f46,f45,f44,f43])).

fof(f79,plain,(
    r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f56])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f82,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f83,plain,(
    v1_funct_1(sK7) ),
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

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f30])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(cnf_transformation,[],[f32])).

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
    inference(cnf_transformation,[],[f32])).

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
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f37])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f54,f56])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(equality_resolution,[],[f67])).

fof(f86,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f49])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_13,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,negated_conjecture,
    ( r1_subset_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_477,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_478,plain,
    ( r1_xboole_0(sK4,sK5)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_480,plain,
    ( r1_xboole_0(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_33,c_31])).

cnf(c_2182,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_8,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2206,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3057,plain,
    ( k4_xboole_0(sK4,sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_2182,c_2206])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2190,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2205,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4151,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK5)) = k9_subset_1(sK2,X0,sK5) ),
    inference(superposition,[status(thm)],[c_2190,c_2205])).

cnf(c_4192,plain,
    ( k9_subset_1(sK2,sK4,sK5) = k4_xboole_0(sK4,sK4) ),
    inference(superposition,[status(thm)],[c_3057,c_4151])).

cnf(c_6,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2208,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3056,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_2208,c_2206])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3146,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3056,c_5])).

cnf(c_4203,plain,
    ( k9_subset_1(sK2,sK4,sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4192,c_3146])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2193,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2201,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4546,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0)
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_2201])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_43,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4701,plain,
    ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4546,c_43])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2196,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4545,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_2201])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_46,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4679,plain,
    ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4545,c_46])).

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
    inference(cnf_transformation,[],[f93])).

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
    inference(cnf_transformation,[],[f70])).

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
    inference(cnf_transformation,[],[f71])).

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
    inference(cnf_transformation,[],[f72])).

cnf(c_199,plain,
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

cnf(c_200,plain,
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
    inference(renaming,[status(thm)],[c_199])).

cnf(c_2183,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_200])).

cnf(c_4685,plain,
    ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4679,c_2183])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_37,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_40,plain,
    ( v1_xboole_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_47,plain,
    ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_48,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7384,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4685,c_37,c_40,c_46,c_47,c_48])).

cnf(c_7385,plain,
    ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7384])).

cnf(c_7391,plain,
    ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4701,c_7385])).

cnf(c_38,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_44,plain,
    ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_45,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2298,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2299,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2298])).

cnf(c_7411,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7391,c_38,c_43,c_44,c_45,c_2299])).

cnf(c_7412,plain,
    ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7411])).

cnf(c_7417,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4203,c_7412])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2202,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3379,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2196,c_2202])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2211,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
    | ~ r1_xboole_0(X1,X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2210,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3929,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,sK4)) != iProver_top
    | r1_xboole_0(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3057,c_2210])).

cnf(c_3932,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r1_xboole_0(sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3929,c_3146])).

cnf(c_479,plain,
    ( r1_xboole_0(sK4,sK5) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_3958,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3932,c_38,c_40,c_479])).

cnf(c_3965,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2211,c_3958])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2203,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4158,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_2203])).

cnf(c_5091,plain,
    ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3379,c_4158])).

cnf(c_3380,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_2202])).

cnf(c_5092,plain,
    ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3380,c_4158])).

cnf(c_7418,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7417,c_4203,c_5091,c_5092])).

cnf(c_7419,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7418])).

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
    inference(cnf_transformation,[],[f94])).

cnf(c_192,plain,
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

cnf(c_193,plain,
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
    inference(renaming,[status(thm)],[c_192])).

cnf(c_2184,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_4684,plain,
    ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | v1_funct_2(sK7,sK5,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4679,c_2184])).

cnf(c_7293,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
    | k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4684,c_37,c_40,c_46,c_47,c_48])).

cnf(c_7294,plain,
    ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
    | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
    | v1_funct_2(X1,X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X2) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7293])).

cnf(c_7300,plain,
    ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | v1_funct_2(sK6,sK4,sK3) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4701,c_7294])).

cnf(c_7320,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7300,c_38,c_43,c_44,c_45,c_2299])).

cnf(c_7321,plain,
    ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
    | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7320])).

cnf(c_7326,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4203,c_7321])).

cnf(c_7327,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7326,c_4203,c_5091,c_5092])).

cnf(c_7328,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
    | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7327])).

cnf(c_22,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_4682,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_4679,c_22])).

cnf(c_4683,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4682,c_4203])).

cnf(c_4812,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4683,c_4701])).

cnf(c_6478,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5091,c_4812])).

cnf(c_6479,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6478,c_5092])).

cnf(c_6480,plain,
    ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
    | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 ),
    inference(equality_resolution_simp,[status(thm)],[c_6479])).

cnf(c_41,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_39,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7419,c_7328,c_6480,c_41,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:04:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.88/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.88/0.97  
% 3.88/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/0.97  
% 3.88/0.97  ------  iProver source info
% 3.88/0.97  
% 3.88/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.88/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/0.97  git: non_committed_changes: false
% 3.88/0.97  git: last_make_outside_of_git: false
% 3.88/0.97  
% 3.88/0.97  ------ 
% 3.88/0.97  
% 3.88/0.97  ------ Input Options
% 3.88/0.97  
% 3.88/0.97  --out_options                           all
% 3.88/0.97  --tptp_safe_out                         true
% 3.88/0.97  --problem_path                          ""
% 3.88/0.97  --include_path                          ""
% 3.88/0.97  --clausifier                            res/vclausify_rel
% 3.88/0.97  --clausifier_options                    ""
% 3.88/0.97  --stdin                                 false
% 3.88/0.97  --stats_out                             all
% 3.88/0.97  
% 3.88/0.97  ------ General Options
% 3.88/0.97  
% 3.88/0.97  --fof                                   false
% 3.88/0.97  --time_out_real                         305.
% 3.88/0.97  --time_out_virtual                      -1.
% 3.88/0.97  --symbol_type_check                     false
% 3.88/0.97  --clausify_out                          false
% 3.88/0.97  --sig_cnt_out                           false
% 3.88/0.97  --trig_cnt_out                          false
% 3.88/0.97  --trig_cnt_out_tolerance                1.
% 3.88/0.97  --trig_cnt_out_sk_spl                   false
% 3.88/0.97  --abstr_cl_out                          false
% 3.88/0.97  
% 3.88/0.97  ------ Global Options
% 3.88/0.97  
% 3.88/0.97  --schedule                              default
% 3.88/0.97  --add_important_lit                     false
% 3.88/0.97  --prop_solver_per_cl                    1000
% 3.88/0.97  --min_unsat_core                        false
% 3.88/0.97  --soft_assumptions                      false
% 3.88/0.97  --soft_lemma_size                       3
% 3.88/0.97  --prop_impl_unit_size                   0
% 3.88/0.97  --prop_impl_unit                        []
% 3.88/0.97  --share_sel_clauses                     true
% 3.88/0.97  --reset_solvers                         false
% 3.88/0.97  --bc_imp_inh                            [conj_cone]
% 3.88/0.97  --conj_cone_tolerance                   3.
% 3.88/0.97  --extra_neg_conj                        none
% 3.88/0.97  --large_theory_mode                     true
% 3.88/0.97  --prolific_symb_bound                   200
% 3.88/0.97  --lt_threshold                          2000
% 3.88/0.97  --clause_weak_htbl                      true
% 3.88/0.97  --gc_record_bc_elim                     false
% 3.88/0.97  
% 3.88/0.98  ------ Preprocessing Options
% 3.88/0.98  
% 3.88/0.98  --preprocessing_flag                    true
% 3.88/0.98  --time_out_prep_mult                    0.1
% 3.88/0.98  --splitting_mode                        input
% 3.88/0.98  --splitting_grd                         true
% 3.88/0.98  --splitting_cvd                         false
% 3.88/0.98  --splitting_cvd_svl                     false
% 3.88/0.98  --splitting_nvd                         32
% 3.88/0.98  --sub_typing                            true
% 3.88/0.98  --prep_gs_sim                           true
% 3.88/0.98  --prep_unflatten                        true
% 3.88/0.98  --prep_res_sim                          true
% 3.88/0.98  --prep_upred                            true
% 3.88/0.98  --prep_sem_filter                       exhaustive
% 3.88/0.98  --prep_sem_filter_out                   false
% 3.88/0.98  --pred_elim                             true
% 3.88/0.98  --res_sim_input                         true
% 3.88/0.98  --eq_ax_congr_red                       true
% 3.88/0.98  --pure_diseq_elim                       true
% 3.88/0.98  --brand_transform                       false
% 3.88/0.98  --non_eq_to_eq                          false
% 3.88/0.98  --prep_def_merge                        true
% 3.88/0.98  --prep_def_merge_prop_impl              false
% 3.88/0.98  --prep_def_merge_mbd                    true
% 3.88/0.98  --prep_def_merge_tr_red                 false
% 3.88/0.98  --prep_def_merge_tr_cl                  false
% 3.88/0.98  --smt_preprocessing                     true
% 3.88/0.98  --smt_ac_axioms                         fast
% 3.88/0.98  --preprocessed_out                      false
% 3.88/0.98  --preprocessed_stats                    false
% 3.88/0.98  
% 3.88/0.98  ------ Abstraction refinement Options
% 3.88/0.98  
% 3.88/0.98  --abstr_ref                             []
% 3.88/0.98  --abstr_ref_prep                        false
% 3.88/0.98  --abstr_ref_until_sat                   false
% 3.88/0.98  --abstr_ref_sig_restrict                funpre
% 3.88/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.88/0.98  --abstr_ref_under                       []
% 3.88/0.98  
% 3.88/0.98  ------ SAT Options
% 3.88/0.98  
% 3.88/0.98  --sat_mode                              false
% 3.88/0.98  --sat_fm_restart_options                ""
% 3.88/0.98  --sat_gr_def                            false
% 3.88/0.98  --sat_epr_types                         true
% 3.88/0.98  --sat_non_cyclic_types                  false
% 3.88/0.98  --sat_finite_models                     false
% 3.88/0.98  --sat_fm_lemmas                         false
% 3.88/0.98  --sat_fm_prep                           false
% 3.88/0.98  --sat_fm_uc_incr                        true
% 3.88/0.98  --sat_out_model                         small
% 3.88/0.98  --sat_out_clauses                       false
% 3.88/0.98  
% 3.88/0.98  ------ QBF Options
% 3.88/0.98  
% 3.88/0.98  --qbf_mode                              false
% 3.88/0.98  --qbf_elim_univ                         false
% 3.88/0.98  --qbf_dom_inst                          none
% 3.88/0.98  --qbf_dom_pre_inst                      false
% 3.88/0.98  --qbf_sk_in                             false
% 3.88/0.98  --qbf_pred_elim                         true
% 3.88/0.98  --qbf_split                             512
% 3.88/0.98  
% 3.88/0.98  ------ BMC1 Options
% 3.88/0.98  
% 3.88/0.98  --bmc1_incremental                      false
% 3.88/0.98  --bmc1_axioms                           reachable_all
% 3.88/0.98  --bmc1_min_bound                        0
% 3.88/0.98  --bmc1_max_bound                        -1
% 3.88/0.98  --bmc1_max_bound_default                -1
% 3.88/0.98  --bmc1_symbol_reachability              true
% 3.88/0.98  --bmc1_property_lemmas                  false
% 3.88/0.98  --bmc1_k_induction                      false
% 3.88/0.98  --bmc1_non_equiv_states                 false
% 3.88/0.98  --bmc1_deadlock                         false
% 3.88/0.98  --bmc1_ucm                              false
% 3.88/0.98  --bmc1_add_unsat_core                   none
% 3.88/0.98  --bmc1_unsat_core_children              false
% 3.88/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.88/0.98  --bmc1_out_stat                         full
% 3.88/0.98  --bmc1_ground_init                      false
% 3.88/0.98  --bmc1_pre_inst_next_state              false
% 3.88/0.98  --bmc1_pre_inst_state                   false
% 3.88/0.98  --bmc1_pre_inst_reach_state             false
% 3.88/0.98  --bmc1_out_unsat_core                   false
% 3.88/0.98  --bmc1_aig_witness_out                  false
% 3.88/0.98  --bmc1_verbose                          false
% 3.88/0.98  --bmc1_dump_clauses_tptp                false
% 3.88/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.88/0.98  --bmc1_dump_file                        -
% 3.88/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.88/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.88/0.98  --bmc1_ucm_extend_mode                  1
% 3.88/0.98  --bmc1_ucm_init_mode                    2
% 3.88/0.98  --bmc1_ucm_cone_mode                    none
% 3.88/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.88/0.98  --bmc1_ucm_relax_model                  4
% 3.88/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.88/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.88/0.98  --bmc1_ucm_layered_model                none
% 3.88/0.98  --bmc1_ucm_max_lemma_size               10
% 3.88/0.98  
% 3.88/0.98  ------ AIG Options
% 3.88/0.98  
% 3.88/0.98  --aig_mode                              false
% 3.88/0.98  
% 3.88/0.98  ------ Instantiation Options
% 3.88/0.98  
% 3.88/0.98  --instantiation_flag                    true
% 3.88/0.98  --inst_sos_flag                         true
% 3.88/0.98  --inst_sos_phase                        true
% 3.88/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.88/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.88/0.98  --inst_lit_sel_side                     num_symb
% 3.88/0.98  --inst_solver_per_active                1400
% 3.88/0.98  --inst_solver_calls_frac                1.
% 3.88/0.98  --inst_passive_queue_type               priority_queues
% 3.88/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.88/0.98  --inst_passive_queues_freq              [25;2]
% 3.88/0.98  --inst_dismatching                      true
% 3.88/0.98  --inst_eager_unprocessed_to_passive     true
% 3.88/0.98  --inst_prop_sim_given                   true
% 3.88/0.98  --inst_prop_sim_new                     false
% 3.88/0.98  --inst_subs_new                         false
% 3.88/0.98  --inst_eq_res_simp                      false
% 3.88/0.98  --inst_subs_given                       false
% 3.88/0.98  --inst_orphan_elimination               true
% 3.88/0.98  --inst_learning_loop_flag               true
% 3.88/0.98  --inst_learning_start                   3000
% 3.88/0.98  --inst_learning_factor                  2
% 3.88/0.98  --inst_start_prop_sim_after_learn       3
% 3.88/0.98  --inst_sel_renew                        solver
% 3.88/0.98  --inst_lit_activity_flag                true
% 3.88/0.98  --inst_restr_to_given                   false
% 3.88/0.98  --inst_activity_threshold               500
% 3.88/0.98  --inst_out_proof                        true
% 3.88/0.98  
% 3.88/0.98  ------ Resolution Options
% 3.88/0.98  
% 3.88/0.98  --resolution_flag                       true
% 3.88/0.98  --res_lit_sel                           adaptive
% 3.88/0.98  --res_lit_sel_side                      none
% 3.88/0.98  --res_ordering                          kbo
% 3.88/0.98  --res_to_prop_solver                    active
% 3.88/0.98  --res_prop_simpl_new                    false
% 3.88/0.98  --res_prop_simpl_given                  true
% 3.88/0.98  --res_passive_queue_type                priority_queues
% 3.88/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.88/0.98  --res_passive_queues_freq               [15;5]
% 3.88/0.98  --res_forward_subs                      full
% 3.88/0.98  --res_backward_subs                     full
% 3.88/0.98  --res_forward_subs_resolution           true
% 3.88/0.98  --res_backward_subs_resolution          true
% 3.88/0.98  --res_orphan_elimination                true
% 3.88/0.98  --res_time_limit                        2.
% 3.88/0.98  --res_out_proof                         true
% 3.88/0.98  
% 3.88/0.98  ------ Superposition Options
% 3.88/0.98  
% 3.88/0.98  --superposition_flag                    true
% 3.88/0.98  --sup_passive_queue_type                priority_queues
% 3.88/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.88/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.88/0.98  --demod_completeness_check              fast
% 3.88/0.98  --demod_use_ground                      true
% 3.88/0.98  --sup_to_prop_solver                    passive
% 3.88/0.98  --sup_prop_simpl_new                    true
% 3.88/0.98  --sup_prop_simpl_given                  true
% 3.88/0.98  --sup_fun_splitting                     true
% 3.88/0.98  --sup_smt_interval                      50000
% 3.88/0.98  
% 3.88/0.98  ------ Superposition Simplification Setup
% 3.88/0.98  
% 3.88/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.88/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.88/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.88/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.88/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.88/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.88/0.98  --sup_immed_triv                        [TrivRules]
% 3.88/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/0.98  --sup_immed_bw_main                     []
% 3.88/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.88/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.88/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/0.98  --sup_input_bw                          []
% 3.88/0.98  
% 3.88/0.98  ------ Combination Options
% 3.88/0.98  
% 3.88/0.98  --comb_res_mult                         3
% 3.88/0.98  --comb_sup_mult                         2
% 3.88/0.98  --comb_inst_mult                        10
% 3.88/0.98  
% 3.88/0.98  ------ Debug Options
% 3.88/0.98  
% 3.88/0.98  --dbg_backtrace                         false
% 3.88/0.98  --dbg_dump_prop_clauses                 false
% 3.88/0.98  --dbg_dump_prop_clauses_file            -
% 3.88/0.98  --dbg_out_stat                          false
% 3.88/0.98  ------ Parsing...
% 3.88/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/0.98  ------ Proving...
% 3.88/0.98  ------ Problem Properties 
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  clauses                                 34
% 3.88/0.98  conjectures                             13
% 3.88/0.98  EPR                                     11
% 3.88/0.98  Horn                                    25
% 3.88/0.98  unary                                   15
% 3.88/0.98  binary                                  8
% 3.88/0.98  lits                                    130
% 3.88/0.98  lits eq                                 15
% 3.88/0.98  fd_pure                                 0
% 3.88/0.98  fd_pseudo                               0
% 3.88/0.98  fd_cond                                 0
% 3.88/0.98  fd_pseudo_cond                          0
% 3.88/0.98  AC symbols                              0
% 3.88/0.98  
% 3.88/0.98  ------ Schedule dynamic 5 is on 
% 3.88/0.98  
% 3.88/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  ------ 
% 3.88/0.98  Current options:
% 3.88/0.98  ------ 
% 3.88/0.98  
% 3.88/0.98  ------ Input Options
% 3.88/0.98  
% 3.88/0.98  --out_options                           all
% 3.88/0.98  --tptp_safe_out                         true
% 3.88/0.98  --problem_path                          ""
% 3.88/0.98  --include_path                          ""
% 3.88/0.98  --clausifier                            res/vclausify_rel
% 3.88/0.98  --clausifier_options                    ""
% 3.88/0.98  --stdin                                 false
% 3.88/0.98  --stats_out                             all
% 3.88/0.98  
% 3.88/0.98  ------ General Options
% 3.88/0.98  
% 3.88/0.98  --fof                                   false
% 3.88/0.98  --time_out_real                         305.
% 3.88/0.98  --time_out_virtual                      -1.
% 3.88/0.98  --symbol_type_check                     false
% 3.88/0.98  --clausify_out                          false
% 3.88/0.98  --sig_cnt_out                           false
% 3.88/0.98  --trig_cnt_out                          false
% 3.88/0.98  --trig_cnt_out_tolerance                1.
% 3.88/0.98  --trig_cnt_out_sk_spl                   false
% 3.88/0.98  --abstr_cl_out                          false
% 3.88/0.98  
% 3.88/0.98  ------ Global Options
% 3.88/0.98  
% 3.88/0.98  --schedule                              default
% 3.88/0.98  --add_important_lit                     false
% 3.88/0.98  --prop_solver_per_cl                    1000
% 3.88/0.98  --min_unsat_core                        false
% 3.88/0.98  --soft_assumptions                      false
% 3.88/0.98  --soft_lemma_size                       3
% 3.88/0.98  --prop_impl_unit_size                   0
% 3.88/0.98  --prop_impl_unit                        []
% 3.88/0.98  --share_sel_clauses                     true
% 3.88/0.98  --reset_solvers                         false
% 3.88/0.98  --bc_imp_inh                            [conj_cone]
% 3.88/0.98  --conj_cone_tolerance                   3.
% 3.88/0.98  --extra_neg_conj                        none
% 3.88/0.98  --large_theory_mode                     true
% 3.88/0.98  --prolific_symb_bound                   200
% 3.88/0.98  --lt_threshold                          2000
% 3.88/0.98  --clause_weak_htbl                      true
% 3.88/0.98  --gc_record_bc_elim                     false
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing Options
% 3.88/0.98  
% 3.88/0.98  --preprocessing_flag                    true
% 3.88/0.98  --time_out_prep_mult                    0.1
% 3.88/0.98  --splitting_mode                        input
% 3.88/0.98  --splitting_grd                         true
% 3.88/0.98  --splitting_cvd                         false
% 3.88/0.98  --splitting_cvd_svl                     false
% 3.88/0.98  --splitting_nvd                         32
% 3.88/0.98  --sub_typing                            true
% 3.88/0.98  --prep_gs_sim                           true
% 3.88/0.98  --prep_unflatten                        true
% 3.88/0.98  --prep_res_sim                          true
% 3.88/0.98  --prep_upred                            true
% 3.88/0.98  --prep_sem_filter                       exhaustive
% 3.88/0.98  --prep_sem_filter_out                   false
% 3.88/0.98  --pred_elim                             true
% 3.88/0.98  --res_sim_input                         true
% 3.88/0.98  --eq_ax_congr_red                       true
% 3.88/0.98  --pure_diseq_elim                       true
% 3.88/0.98  --brand_transform                       false
% 3.88/0.98  --non_eq_to_eq                          false
% 3.88/0.98  --prep_def_merge                        true
% 3.88/0.98  --prep_def_merge_prop_impl              false
% 3.88/0.98  --prep_def_merge_mbd                    true
% 3.88/0.98  --prep_def_merge_tr_red                 false
% 3.88/0.98  --prep_def_merge_tr_cl                  false
% 3.88/0.98  --smt_preprocessing                     true
% 3.88/0.98  --smt_ac_axioms                         fast
% 3.88/0.98  --preprocessed_out                      false
% 3.88/0.98  --preprocessed_stats                    false
% 3.88/0.98  
% 3.88/0.98  ------ Abstraction refinement Options
% 3.88/0.98  
% 3.88/0.98  --abstr_ref                             []
% 3.88/0.98  --abstr_ref_prep                        false
% 3.88/0.98  --abstr_ref_until_sat                   false
% 3.88/0.98  --abstr_ref_sig_restrict                funpre
% 3.88/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.88/0.98  --abstr_ref_under                       []
% 3.88/0.98  
% 3.88/0.98  ------ SAT Options
% 3.88/0.98  
% 3.88/0.98  --sat_mode                              false
% 3.88/0.98  --sat_fm_restart_options                ""
% 3.88/0.98  --sat_gr_def                            false
% 3.88/0.98  --sat_epr_types                         true
% 3.88/0.98  --sat_non_cyclic_types                  false
% 3.88/0.98  --sat_finite_models                     false
% 3.88/0.98  --sat_fm_lemmas                         false
% 3.88/0.98  --sat_fm_prep                           false
% 3.88/0.98  --sat_fm_uc_incr                        true
% 3.88/0.98  --sat_out_model                         small
% 3.88/0.98  --sat_out_clauses                       false
% 3.88/0.98  
% 3.88/0.98  ------ QBF Options
% 3.88/0.98  
% 3.88/0.98  --qbf_mode                              false
% 3.88/0.98  --qbf_elim_univ                         false
% 3.88/0.98  --qbf_dom_inst                          none
% 3.88/0.98  --qbf_dom_pre_inst                      false
% 3.88/0.98  --qbf_sk_in                             false
% 3.88/0.98  --qbf_pred_elim                         true
% 3.88/0.98  --qbf_split                             512
% 3.88/0.98  
% 3.88/0.98  ------ BMC1 Options
% 3.88/0.98  
% 3.88/0.98  --bmc1_incremental                      false
% 3.88/0.98  --bmc1_axioms                           reachable_all
% 3.88/0.98  --bmc1_min_bound                        0
% 3.88/0.98  --bmc1_max_bound                        -1
% 3.88/0.98  --bmc1_max_bound_default                -1
% 3.88/0.98  --bmc1_symbol_reachability              true
% 3.88/0.98  --bmc1_property_lemmas                  false
% 3.88/0.98  --bmc1_k_induction                      false
% 3.88/0.98  --bmc1_non_equiv_states                 false
% 3.88/0.98  --bmc1_deadlock                         false
% 3.88/0.98  --bmc1_ucm                              false
% 3.88/0.98  --bmc1_add_unsat_core                   none
% 3.88/0.98  --bmc1_unsat_core_children              false
% 3.88/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.88/0.98  --bmc1_out_stat                         full
% 3.88/0.98  --bmc1_ground_init                      false
% 3.88/0.98  --bmc1_pre_inst_next_state              false
% 3.88/0.98  --bmc1_pre_inst_state                   false
% 3.88/0.98  --bmc1_pre_inst_reach_state             false
% 3.88/0.98  --bmc1_out_unsat_core                   false
% 3.88/0.98  --bmc1_aig_witness_out                  false
% 3.88/0.98  --bmc1_verbose                          false
% 3.88/0.98  --bmc1_dump_clauses_tptp                false
% 3.88/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.88/0.98  --bmc1_dump_file                        -
% 3.88/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.88/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.88/0.98  --bmc1_ucm_extend_mode                  1
% 3.88/0.98  --bmc1_ucm_init_mode                    2
% 3.88/0.98  --bmc1_ucm_cone_mode                    none
% 3.88/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.88/0.98  --bmc1_ucm_relax_model                  4
% 3.88/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.88/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.88/0.98  --bmc1_ucm_layered_model                none
% 3.88/0.98  --bmc1_ucm_max_lemma_size               10
% 3.88/0.98  
% 3.88/0.98  ------ AIG Options
% 3.88/0.98  
% 3.88/0.98  --aig_mode                              false
% 3.88/0.98  
% 3.88/0.98  ------ Instantiation Options
% 3.88/0.98  
% 3.88/0.98  --instantiation_flag                    true
% 3.88/0.98  --inst_sos_flag                         true
% 3.88/0.98  --inst_sos_phase                        true
% 3.88/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.88/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.88/0.98  --inst_lit_sel_side                     none
% 3.88/0.98  --inst_solver_per_active                1400
% 3.88/0.98  --inst_solver_calls_frac                1.
% 3.88/0.98  --inst_passive_queue_type               priority_queues
% 3.88/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.88/0.98  --inst_passive_queues_freq              [25;2]
% 3.88/0.98  --inst_dismatching                      true
% 3.88/0.98  --inst_eager_unprocessed_to_passive     true
% 3.88/0.98  --inst_prop_sim_given                   true
% 3.88/0.98  --inst_prop_sim_new                     false
% 3.88/0.98  --inst_subs_new                         false
% 3.88/0.98  --inst_eq_res_simp                      false
% 3.88/0.98  --inst_subs_given                       false
% 3.88/0.98  --inst_orphan_elimination               true
% 3.88/0.98  --inst_learning_loop_flag               true
% 3.88/0.98  --inst_learning_start                   3000
% 3.88/0.98  --inst_learning_factor                  2
% 3.88/0.98  --inst_start_prop_sim_after_learn       3
% 3.88/0.98  --inst_sel_renew                        solver
% 3.88/0.98  --inst_lit_activity_flag                true
% 3.88/0.98  --inst_restr_to_given                   false
% 3.88/0.98  --inst_activity_threshold               500
% 3.88/0.98  --inst_out_proof                        true
% 3.88/0.98  
% 3.88/0.98  ------ Resolution Options
% 3.88/0.98  
% 3.88/0.98  --resolution_flag                       false
% 3.88/0.98  --res_lit_sel                           adaptive
% 3.88/0.98  --res_lit_sel_side                      none
% 3.88/0.98  --res_ordering                          kbo
% 3.88/0.98  --res_to_prop_solver                    active
% 3.88/0.98  --res_prop_simpl_new                    false
% 3.88/0.98  --res_prop_simpl_given                  true
% 3.88/0.98  --res_passive_queue_type                priority_queues
% 3.88/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.88/0.98  --res_passive_queues_freq               [15;5]
% 3.88/0.98  --res_forward_subs                      full
% 3.88/0.98  --res_backward_subs                     full
% 3.88/0.98  --res_forward_subs_resolution           true
% 3.88/0.98  --res_backward_subs_resolution          true
% 3.88/0.98  --res_orphan_elimination                true
% 3.88/0.98  --res_time_limit                        2.
% 3.88/0.98  --res_out_proof                         true
% 3.88/0.98  
% 3.88/0.98  ------ Superposition Options
% 3.88/0.98  
% 3.88/0.98  --superposition_flag                    true
% 3.88/0.98  --sup_passive_queue_type                priority_queues
% 3.88/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.88/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.88/0.98  --demod_completeness_check              fast
% 3.88/0.98  --demod_use_ground                      true
% 3.88/0.98  --sup_to_prop_solver                    passive
% 3.88/0.98  --sup_prop_simpl_new                    true
% 3.88/0.98  --sup_prop_simpl_given                  true
% 3.88/0.98  --sup_fun_splitting                     true
% 3.88/0.98  --sup_smt_interval                      50000
% 3.88/0.98  
% 3.88/0.98  ------ Superposition Simplification Setup
% 3.88/0.98  
% 3.88/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.88/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.88/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.88/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.88/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.88/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.88/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.88/0.98  --sup_immed_triv                        [TrivRules]
% 3.88/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/0.98  --sup_immed_bw_main                     []
% 3.88/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.88/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.88/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.88/0.98  --sup_input_bw                          []
% 3.88/0.98  
% 3.88/0.98  ------ Combination Options
% 3.88/0.98  
% 3.88/0.98  --comb_res_mult                         3
% 3.88/0.98  --comb_sup_mult                         2
% 3.88/0.98  --comb_inst_mult                        10
% 3.88/0.98  
% 3.88/0.98  ------ Debug Options
% 3.88/0.98  
% 3.88/0.98  --dbg_backtrace                         false
% 3.88/0.98  --dbg_dump_prop_clauses                 false
% 3.88/0.98  --dbg_dump_prop_clauses_file            -
% 3.88/0.98  --dbg_out_stat                          false
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  ------ Proving...
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  % SZS status Theorem for theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  fof(f10,axiom,(
% 3.88/0.98    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f24,plain,(
% 3.88/0.98    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.88/0.98    inference(ennf_transformation,[],[f10])).
% 3.88/0.98  
% 3.88/0.98  fof(f25,plain,(
% 3.88/0.98    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.88/0.98    inference(flattening,[],[f24])).
% 3.88/0.98  
% 3.88/0.98  fof(f40,plain,(
% 3.88/0.98    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.88/0.98    inference(nnf_transformation,[],[f25])).
% 3.88/0.98  
% 3.88/0.98  fof(f63,plain,(
% 3.88/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f40])).
% 3.88/0.98  
% 3.88/0.98  fof(f15,conjecture,(
% 3.88/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f16,negated_conjecture,(
% 3.88/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.88/0.98    inference(negated_conjecture,[],[f15])).
% 3.88/0.98  
% 3.88/0.98  fof(f33,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f16])).
% 3.88/0.98  
% 3.88/0.98  fof(f34,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.88/0.98    inference(flattening,[],[f33])).
% 3.88/0.98  
% 3.88/0.98  fof(f48,plain,(
% 3.88/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X3) != sK7 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK7),X2) != X4 | k2_partfun1(X3,X1,sK7,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK7,X3,X1) & v1_funct_1(sK7))) )),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f47,plain,(
% 3.88/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK6,X5),X2) != sK6 | k2_partfun1(X2,X1,sK6,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK6,X2,X1) & v1_funct_1(sK6))) )),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f46,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),sK5) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK5),X1,k1_tmap_1(X0,X1,X2,sK5,X4,X5),X2) != X4 | k2_partfun1(sK5,X1,X5,k9_subset_1(X0,X2,sK5)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK5))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK5,X1))) & v1_funct_2(X5,sK5,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK5) & m1_subset_1(sK5,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK5))) )),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f45,plain,(
% 3.88/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK4,X3),X1,k1_tmap_1(X0,X1,sK4,X3,X4,X5),sK4) != X4 | k2_partfun1(sK4,X1,X4,k9_subset_1(X0,sK4,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK4,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK4,X1))) & v1_funct_2(X4,sK4,X1) & v1_funct_1(X4)) & r1_subset_1(sK4,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK4))) )),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f44,plain,(
% 3.88/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK3,k1_tmap_1(X0,sK3,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK3,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK3,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK3))) & v1_funct_2(X5,X3,sK3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK3))) & v1_funct_2(X4,X2,sK3) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK3))) )),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f43,plain,(
% 3.88/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK2,X2,X3),X1,k1_tmap_1(sK2,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK2,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK2,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK2)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK2))),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f49,plain,(
% 3.88/0.98    ((((((k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) & v1_funct_2(sK7,sK5,sK3) & v1_funct_1(sK7)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) & v1_funct_2(sK6,sK4,sK3) & v1_funct_1(sK6)) & r1_subset_1(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(sK2)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)) & ~v1_xboole_0(sK2)),
% 3.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f34,f48,f47,f46,f45,f44,f43])).
% 3.88/0.98  
% 3.88/0.98  fof(f79,plain,(
% 3.88/0.98    r1_subset_1(sK4,sK5)),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f75,plain,(
% 3.88/0.98    ~v1_xboole_0(sK4)),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f77,plain,(
% 3.88/0.98    ~v1_xboole_0(sK5)),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f6,axiom,(
% 3.88/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f39,plain,(
% 3.88/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.88/0.98    inference(nnf_transformation,[],[f6])).
% 3.88/0.98  
% 3.88/0.98  fof(f58,plain,(
% 3.88/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f39])).
% 3.88/0.98  
% 3.88/0.98  fof(f78,plain,(
% 3.88/0.98    m1_subset_1(sK5,k1_zfmisc_1(sK2))),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f7,axiom,(
% 3.88/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f21,plain,(
% 3.88/0.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.88/0.98    inference(ennf_transformation,[],[f7])).
% 3.88/0.98  
% 3.88/0.98  fof(f60,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.88/0.98    inference(cnf_transformation,[],[f21])).
% 3.88/0.98  
% 3.88/0.98  fof(f4,axiom,(
% 3.88/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f56,plain,(
% 3.88/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.88/0.98    inference(cnf_transformation,[],[f4])).
% 3.88/0.98  
% 3.88/0.98  fof(f90,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.88/0.98    inference(definition_unfolding,[],[f60,f56])).
% 3.88/0.98  
% 3.88/0.98  fof(f5,axiom,(
% 3.88/0.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f57,plain,(
% 3.88/0.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f5])).
% 3.88/0.98  
% 3.88/0.98  fof(f3,axiom,(
% 3.88/0.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f55,plain,(
% 3.88/0.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.88/0.98    inference(cnf_transformation,[],[f3])).
% 3.88/0.98  
% 3.88/0.98  fof(f89,plain,(
% 3.88/0.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.88/0.98    inference(definition_unfolding,[],[f55,f56])).
% 3.88/0.98  
% 3.88/0.98  fof(f82,plain,(
% 3.88/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3)))),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f12,axiom,(
% 3.88/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f27,plain,(
% 3.88/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.88/0.98    inference(ennf_transformation,[],[f12])).
% 3.88/0.98  
% 3.88/0.98  fof(f28,plain,(
% 3.88/0.98    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.88/0.98    inference(flattening,[],[f27])).
% 3.88/0.98  
% 3.88/0.98  fof(f66,plain,(
% 3.88/0.98    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f28])).
% 3.88/0.98  
% 3.88/0.98  fof(f80,plain,(
% 3.88/0.98    v1_funct_1(sK6)),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f85,plain,(
% 3.88/0.98    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3)))),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f83,plain,(
% 3.88/0.98    v1_funct_1(sK7)),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f13,axiom,(
% 3.88/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f29,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f13])).
% 3.88/0.98  
% 3.88/0.98  fof(f30,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.88/0.98    inference(flattening,[],[f29])).
% 3.88/0.98  
% 3.88/0.98  fof(f41,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.88/0.98    inference(nnf_transformation,[],[f30])).
% 3.88/0.98  
% 3.88/0.98  fof(f42,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.88/0.98    inference(flattening,[],[f41])).
% 3.88/0.98  
% 3.88/0.98  fof(f68,plain,(
% 3.88/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f42])).
% 3.88/0.98  
% 3.88/0.98  fof(f93,plain,(
% 3.88/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.88/0.98    inference(equality_resolution,[],[f68])).
% 3.88/0.98  
% 3.88/0.98  fof(f14,axiom,(
% 3.88/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f31,plain,(
% 3.88/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.88/0.98    inference(ennf_transformation,[],[f14])).
% 3.88/0.98  
% 3.88/0.98  fof(f32,plain,(
% 3.88/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.88/0.98    inference(flattening,[],[f31])).
% 3.88/0.98  
% 3.88/0.98  fof(f70,plain,(
% 3.88/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f32])).
% 3.88/0.98  
% 3.88/0.98  fof(f71,plain,(
% 3.88/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f32])).
% 3.88/0.98  
% 3.88/0.98  fof(f72,plain,(
% 3.88/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f32])).
% 3.88/0.98  
% 3.88/0.98  fof(f74,plain,(
% 3.88/0.98    ~v1_xboole_0(sK3)),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f84,plain,(
% 3.88/0.98    v1_funct_2(sK7,sK5,sK3)),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f81,plain,(
% 3.88/0.98    v1_funct_2(sK6,sK4,sK3)),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f8,axiom,(
% 3.88/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f22,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f8])).
% 3.88/0.98  
% 3.88/0.98  fof(f61,plain,(
% 3.88/0.98    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f22])).
% 3.88/0.98  
% 3.88/0.98  fof(f11,axiom,(
% 3.88/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f26,plain,(
% 3.88/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.88/0.98    inference(ennf_transformation,[],[f11])).
% 3.88/0.98  
% 3.88/0.98  fof(f65,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.88/0.98    inference(cnf_transformation,[],[f26])).
% 3.88/0.98  
% 3.88/0.98  fof(f1,axiom,(
% 3.88/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f17,plain,(
% 3.88/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.88/0.98    inference(rectify,[],[f1])).
% 3.88/0.98  
% 3.88/0.98  fof(f19,plain,(
% 3.88/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.88/0.98    inference(ennf_transformation,[],[f17])).
% 3.88/0.98  
% 3.88/0.98  fof(f35,plain,(
% 3.88/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f36,plain,(
% 3.88/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f35])).
% 3.88/0.98  
% 3.88/0.98  fof(f50,plain,(
% 3.88/0.98    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f36])).
% 3.88/0.98  
% 3.88/0.98  fof(f2,axiom,(
% 3.88/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f18,plain,(
% 3.88/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 3.88/0.98    inference(rectify,[],[f2])).
% 3.88/0.98  
% 3.88/0.98  fof(f20,plain,(
% 3.88/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.88/0.98    inference(ennf_transformation,[],[f18])).
% 3.88/0.98  
% 3.88/0.98  fof(f37,plain,(
% 3.88/0.98    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)))),
% 3.88/0.98    introduced(choice_axiom,[])).
% 3.88/0.98  
% 3.88/0.98  fof(f38,plain,(
% 3.88/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK1(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 3.88/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f37])).
% 3.88/0.98  
% 3.88/0.98  fof(f54,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 3.88/0.98    inference(cnf_transformation,[],[f38])).
% 3.88/0.98  
% 3.88/0.98  fof(f87,plain,(
% 3.88/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.88/0.98    inference(definition_unfolding,[],[f54,f56])).
% 3.88/0.98  
% 3.88/0.98  fof(f9,axiom,(
% 3.88/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 3.88/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.88/0.98  
% 3.88/0.98  fof(f23,plain,(
% 3.88/0.98    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.88/0.98    inference(ennf_transformation,[],[f9])).
% 3.88/0.98  
% 3.88/0.98  fof(f62,plain,(
% 3.88/0.98    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f23])).
% 3.88/0.98  
% 3.88/0.98  fof(f67,plain,(
% 3.88/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.88/0.98    inference(cnf_transformation,[],[f42])).
% 3.88/0.98  
% 3.88/0.98  fof(f94,plain,(
% 3.88/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.88/0.98    inference(equality_resolution,[],[f67])).
% 3.88/0.98  
% 3.88/0.98  fof(f86,plain,(
% 3.88/0.98    k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7 | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5))),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  fof(f76,plain,(
% 3.88/0.98    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 3.88/0.98    inference(cnf_transformation,[],[f49])).
% 3.88/0.98  
% 3.88/0.98  cnf(c_13,plain,
% 3.88/0.98      ( ~ r1_subset_1(X0,X1)
% 3.88/0.98      | r1_xboole_0(X0,X1)
% 3.88/0.98      | v1_xboole_0(X0)
% 3.88/0.98      | v1_xboole_0(X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_29,negated_conjecture,
% 3.88/0.98      ( r1_subset_1(sK4,sK5) ),
% 3.88/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_477,plain,
% 3.88/0.98      ( r1_xboole_0(X0,X1)
% 3.88/0.98      | v1_xboole_0(X0)
% 3.88/0.98      | v1_xboole_0(X1)
% 3.88/0.98      | sK5 != X1
% 3.88/0.98      | sK4 != X0 ),
% 3.88/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_478,plain,
% 3.88/0.98      ( r1_xboole_0(sK4,sK5) | v1_xboole_0(sK5) | v1_xboole_0(sK4) ),
% 3.88/0.98      inference(unflattening,[status(thm)],[c_477]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_33,negated_conjecture,
% 3.88/0.98      ( ~ v1_xboole_0(sK4) ),
% 3.88/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_31,negated_conjecture,
% 3.88/0.98      ( ~ v1_xboole_0(sK5) ),
% 3.88/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_480,plain,
% 3.88/0.98      ( r1_xboole_0(sK4,sK5) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_478,c_33,c_31]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2182,plain,
% 3.88/0.98      ( r1_xboole_0(sK4,sK5) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_8,plain,
% 3.88/0.98      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2206,plain,
% 3.88/0.98      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3057,plain,
% 3.88/0.98      ( k4_xboole_0(sK4,sK5) = sK4 ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_2182,c_2206]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_30,negated_conjecture,
% 3.88/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) ),
% 3.88/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2190,plain,
% 3.88/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_9,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/0.98      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2205,plain,
% 3.88/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.88/0.98      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4151,plain,
% 3.88/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,sK5)) = k9_subset_1(sK2,X0,sK5) ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_2190,c_2205]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4192,plain,
% 3.88/0.98      ( k9_subset_1(sK2,sK4,sK5) = k4_xboole_0(sK4,sK4) ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3057,c_4151]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6,plain,
% 3.88/0.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2208,plain,
% 3.88/0.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3056,plain,
% 3.88/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_2208,c_2206]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5,plain,
% 3.88/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3146,plain,
% 3.88/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.88/0.98      inference(demodulation,[status(thm)],[c_3056,c_5]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4203,plain,
% 3.88/0.98      ( k9_subset_1(sK2,sK4,sK5) = k1_xboole_0 ),
% 3.88/0.98      inference(demodulation,[status(thm)],[c_4192,c_3146]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_26,negated_conjecture,
% 3.88/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) ),
% 3.88/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2193,plain,
% 3.88/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_15,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | ~ v1_funct_1(X0)
% 3.88/0.98      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 3.88/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2201,plain,
% 3.88/0.98      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 3.88/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.88/0.98      | v1_funct_1(X2) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4546,plain,
% 3.88/0.98      ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0)
% 3.88/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_2193,c_2201]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_28,negated_conjecture,
% 3.88/0.98      ( v1_funct_1(sK6) ),
% 3.88/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_43,plain,
% 3.88/0.98      ( v1_funct_1(sK6) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4701,plain,
% 3.88/0.98      ( k2_partfun1(sK4,sK3,sK6,X0) = k7_relat_1(sK6,X0) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_4546,c_43]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_23,negated_conjecture,
% 3.88/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) ),
% 3.88/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2196,plain,
% 3.88/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4545,plain,
% 3.88/0.98      ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0)
% 3.88/0.98      | v1_funct_1(sK7) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_2196,c_2201]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_25,negated_conjecture,
% 3.88/0.98      ( v1_funct_1(sK7) ),
% 3.88/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_46,plain,
% 3.88/0.98      ( v1_funct_1(sK7) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4679,plain,
% 3.88/0.98      ( k2_partfun1(sK5,sK3,sK7,X0) = k7_relat_1(sK7,X0) ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_4545,c_46]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_17,plain,
% 3.88/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.88/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.88/0.98      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.88/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.88/0.98      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.88/0.98      | ~ v1_funct_1(X0)
% 3.88/0.98      | ~ v1_funct_1(X3)
% 3.88/0.98      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.88/0.98      | v1_xboole_0(X5)
% 3.88/0.98      | v1_xboole_0(X2)
% 3.88/0.98      | v1_xboole_0(X4)
% 3.88/0.98      | v1_xboole_0(X1)
% 3.88/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_21,plain,
% 3.88/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.88/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.88/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.88/0.98      | ~ v1_funct_1(X0)
% 3.88/0.98      | ~ v1_funct_1(X3)
% 3.88/0.98      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.88/0.98      | v1_xboole_0(X5)
% 3.88/0.98      | v1_xboole_0(X2)
% 3.88/0.98      | v1_xboole_0(X4)
% 3.88/0.98      | v1_xboole_0(X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_20,plain,
% 3.88/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.88/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.88/0.98      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.88/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.88/0.98      | ~ v1_funct_1(X0)
% 3.88/0.98      | ~ v1_funct_1(X3)
% 3.88/0.98      | v1_xboole_0(X5)
% 3.88/0.98      | v1_xboole_0(X2)
% 3.88/0.98      | v1_xboole_0(X4)
% 3.88/0.98      | v1_xboole_0(X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_19,plain,
% 3.88/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.88/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.88/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.88/0.98      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.88/0.98      | ~ v1_funct_1(X0)
% 3.88/0.98      | ~ v1_funct_1(X3)
% 3.88/0.98      | v1_xboole_0(X5)
% 3.88/0.98      | v1_xboole_0(X2)
% 3.88/0.98      | v1_xboole_0(X4)
% 3.88/0.98      | v1_xboole_0(X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_199,plain,
% 3.88/0.98      ( ~ v1_funct_1(X3)
% 3.88/0.98      | ~ v1_funct_1(X0)
% 3.88/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.88/0.98      | ~ v1_funct_2(X0,X1,X2)
% 3.88/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.88/0.98      | v1_xboole_0(X5)
% 3.88/0.98      | v1_xboole_0(X2)
% 3.88/0.98      | v1_xboole_0(X4)
% 3.88/0.98      | v1_xboole_0(X1)
% 3.88/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_17,c_21,c_20,c_19]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_200,plain,
% 3.88/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.88/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.88/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.88/0.98      | ~ v1_funct_1(X0)
% 3.88/0.98      | ~ v1_funct_1(X3)
% 3.88/0.98      | v1_xboole_0(X1)
% 3.88/0.98      | v1_xboole_0(X2)
% 3.88/0.98      | v1_xboole_0(X4)
% 3.88/0.98      | v1_xboole_0(X5)
% 3.88/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_199]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2183,plain,
% 3.88/0.98      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 3.88/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.88/0.98      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.88/0.98      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.88/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.88/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.88/0.98      | v1_funct_1(X2) != iProver_top
% 3.88/0.98      | v1_funct_1(X5) != iProver_top
% 3.88/0.98      | v1_xboole_0(X3) = iProver_top
% 3.88/0.98      | v1_xboole_0(X1) = iProver_top
% 3.88/0.98      | v1_xboole_0(X4) = iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_200]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4685,plain,
% 3.88/0.98      ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.88/0.98      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.88/0.98      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.88/0.98      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | v1_funct_1(X1) != iProver_top
% 3.88/0.98      | v1_funct_1(sK7) != iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top
% 3.88/0.98      | v1_xboole_0(X2) = iProver_top
% 3.88/0.98      | v1_xboole_0(sK3) = iProver_top
% 3.88/0.98      | v1_xboole_0(sK5) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_4679,c_2183]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_34,negated_conjecture,
% 3.88/0.98      ( ~ v1_xboole_0(sK3) ),
% 3.88/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_37,plain,
% 3.88/0.98      ( v1_xboole_0(sK3) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_40,plain,
% 3.88/0.98      ( v1_xboole_0(sK5) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_24,negated_conjecture,
% 3.88/0.98      ( v1_funct_2(sK7,sK5,sK3) ),
% 3.88/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_47,plain,
% 3.88/0.98      ( v1_funct_2(sK7,sK5,sK3) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_48,plain,
% 3.88/0.98      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7384,plain,
% 3.88/0.98      ( v1_funct_1(X1) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.88/0.98      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.88/0.98      | k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top
% 3.88/0.98      | v1_xboole_0(X2) = iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_4685,c_37,c_40,c_46,c_47,c_48]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7385,plain,
% 3.88/0.98      ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),sK5) = sK7
% 3.88/0.98      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | v1_funct_1(X1) != iProver_top
% 3.88/0.98      | v1_xboole_0(X2) = iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_7384]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7391,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.88/0.98      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.88/0.98      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.88/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | v1_funct_1(sK6) != iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top
% 3.88/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_4701,c_7385]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_38,plain,
% 3.88/0.98      ( v1_xboole_0(sK4) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_27,negated_conjecture,
% 3.88/0.98      ( v1_funct_2(sK6,sK4,sK3) ),
% 3.88/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_44,plain,
% 3.88/0.98      ( v1_funct_2(sK6,sK4,sK3) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_45,plain,
% 3.88/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_10,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/0.98      | ~ v1_xboole_0(X1)
% 3.88/0.98      | v1_xboole_0(X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2298,plain,
% 3.88/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 3.88/0.98      | ~ v1_xboole_0(X0)
% 3.88/0.98      | v1_xboole_0(sK4) ),
% 3.88/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2299,plain,
% 3.88/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | v1_xboole_0(X0) != iProver_top
% 3.88/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_2298]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7411,plain,
% 3.88/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7 ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_7391,c_38,c_43,c_44,c_45,c_2299]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7412,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.88/0.98      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_7411]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7417,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.88/0.98      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_4203,c_7412]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_14,plain,
% 3.88/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | v1_relat_1(X0) ),
% 3.88/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2202,plain,
% 3.88/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.88/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3379,plain,
% 3.88/0.98      ( v1_relat_1(sK7) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_2196,c_2202]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2,plain,
% 3.88/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.88/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2211,plain,
% 3.88/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.88/0.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3,plain,
% 3.88/0.98      ( ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
% 3.88/0.98      | ~ r1_xboole_0(X1,X2) ),
% 3.88/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2210,plain,
% 3.88/0.98      ( r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) != iProver_top
% 3.88/0.98      | r1_xboole_0(X1,X2) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3929,plain,
% 3.88/0.98      ( r2_hidden(X0,k4_xboole_0(sK4,sK4)) != iProver_top
% 3.88/0.98      | r1_xboole_0(sK4,sK5) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3057,c_2210]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3932,plain,
% 3.88/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.88/0.98      | r1_xboole_0(sK4,sK5) != iProver_top ),
% 3.88/0.98      inference(demodulation,[status(thm)],[c_3929,c_3146]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_479,plain,
% 3.88/0.98      ( r1_xboole_0(sK4,sK5) = iProver_top
% 3.88/0.98      | v1_xboole_0(sK5) = iProver_top
% 3.88/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3958,plain,
% 3.88/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_3932,c_38,c_40,c_479]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3965,plain,
% 3.88/0.98      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_2211,c_3958]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_11,plain,
% 3.88/0.98      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 3.88/0.98      | ~ v1_relat_1(X1)
% 3.88/0.98      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 3.88/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2203,plain,
% 3.88/0.98      ( k7_relat_1(X0,X1) = k1_xboole_0
% 3.88/0.98      | r1_xboole_0(X1,k1_relat_1(X0)) != iProver_top
% 3.88/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4158,plain,
% 3.88/0.98      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 3.88/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3965,c_2203]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5091,plain,
% 3.88/0.98      ( k7_relat_1(sK7,k1_xboole_0) = k1_xboole_0 ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3379,c_4158]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_3380,plain,
% 3.88/0.98      ( v1_relat_1(sK6) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_2193,c_2202]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_5092,plain,
% 3.88/0.98      ( k7_relat_1(sK6,k1_xboole_0) = k1_xboole_0 ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_3380,c_4158]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7418,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.88/0.98      | k1_xboole_0 != k1_xboole_0
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 3.88/0.98      inference(light_normalisation,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_7417,c_4203,c_5091,c_5092]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7419,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) = sK7
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 3.88/0.98      inference(equality_resolution_simp,[status(thm)],[c_7418]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_18,plain,
% 3.88/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.88/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.88/0.98      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 3.88/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.88/0.98      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 3.88/0.98      | ~ v1_funct_1(X0)
% 3.88/0.98      | ~ v1_funct_1(X3)
% 3.88/0.98      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 3.88/0.98      | v1_xboole_0(X5)
% 3.88/0.98      | v1_xboole_0(X2)
% 3.88/0.98      | v1_xboole_0(X4)
% 3.88/0.98      | v1_xboole_0(X1)
% 3.88/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.88/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_192,plain,
% 3.88/0.98      ( ~ v1_funct_1(X3)
% 3.88/0.98      | ~ v1_funct_1(X0)
% 3.88/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.88/0.98      | ~ v1_funct_2(X0,X1,X2)
% 3.88/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.88/0.98      | v1_xboole_0(X5)
% 3.88/0.98      | v1_xboole_0(X2)
% 3.88/0.98      | v1_xboole_0(X4)
% 3.88/0.98      | v1_xboole_0(X1)
% 3.88/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_18,c_21,c_20,c_19]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_193,plain,
% 3.88/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.88/0.98      | ~ v1_funct_2(X3,X4,X2)
% 3.88/0.98      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 3.88/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.88/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.88/0.98      | ~ v1_funct_1(X0)
% 3.88/0.98      | ~ v1_funct_1(X3)
% 3.88/0.98      | v1_xboole_0(X1)
% 3.88/0.98      | v1_xboole_0(X2)
% 3.88/0.98      | v1_xboole_0(X4)
% 3.88/0.98      | v1_xboole_0(X5)
% 3.88/0.98      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_192]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_2184,plain,
% 3.88/0.98      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 3.88/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.88/0.98      | v1_funct_2(X5,X4,X1) != iProver_top
% 3.88/0.98      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 3.88/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.88/0.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 3.88/0.98      | v1_funct_1(X2) != iProver_top
% 3.88/0.98      | v1_funct_1(X5) != iProver_top
% 3.88/0.98      | v1_xboole_0(X3) = iProver_top
% 3.88/0.98      | v1_xboole_0(X1) = iProver_top
% 3.88/0.98      | v1_xboole_0(X4) = iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4684,plain,
% 3.88/0.98      ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.88/0.98      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.88/0.98      | v1_funct_2(sK7,sK5,sK3) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.88/0.98      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK3))) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | v1_funct_1(X1) != iProver_top
% 3.88/0.98      | v1_funct_1(sK7) != iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top
% 3.88/0.98      | v1_xboole_0(X2) = iProver_top
% 3.88/0.98      | v1_xboole_0(sK3) = iProver_top
% 3.88/0.98      | v1_xboole_0(sK5) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_4679,c_2184]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7293,plain,
% 3.88/0.98      ( v1_funct_1(X1) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.88/0.98      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.88/0.98      | k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top
% 3.88/0.98      | v1_xboole_0(X2) = iProver_top ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_4684,c_37,c_40,c_46,c_47,c_48]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7294,plain,
% 3.88/0.98      ( k2_partfun1(X0,sK3,X1,k9_subset_1(X2,X0,sK5)) != k7_relat_1(sK7,k9_subset_1(X2,X0,sK5))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X2,X0,sK5),sK3,k1_tmap_1(X2,sK3,X0,sK5,X1,sK7),X0) = X1
% 3.88/0.98      | v1_funct_2(X1,X0,sK3) != iProver_top
% 3.88/0.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK3))) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X2)) != iProver_top
% 3.88/0.98      | v1_funct_1(X1) != iProver_top
% 3.88/0.98      | v1_xboole_0(X2) = iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_7293]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7300,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.88/0.98      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.88/0.98      | v1_funct_2(sK6,sK4,sK3) != iProver_top
% 3.88/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK3))) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | v1_funct_1(sK6) != iProver_top
% 3.88/0.98      | v1_xboole_0(X0) = iProver_top
% 3.88/0.98      | v1_xboole_0(sK4) = iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_4701,c_7294]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7320,plain,
% 3.88/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.88/0.98      | k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6 ),
% 3.88/0.98      inference(global_propositional_subsumption,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_7300,c_38,c_43,c_44,c_45,c_2299]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7321,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(X0,sK4,sK5),sK3,k1_tmap_1(X0,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.88/0.98      | k7_relat_1(sK7,k9_subset_1(X0,sK4,sK5)) != k7_relat_1(sK6,k9_subset_1(X0,sK4,sK5))
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(X0)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,k1_zfmisc_1(X0)) != iProver_top ),
% 3.88/0.98      inference(renaming,[status(thm)],[c_7320]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7326,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.88/0.98      | k7_relat_1(sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k1_xboole_0)
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 3.88/0.98      inference(superposition,[status(thm)],[c_4203,c_7321]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7327,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.88/0.98      | k1_xboole_0 != k1_xboole_0
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 3.88/0.98      inference(light_normalisation,
% 3.88/0.98                [status(thm)],
% 3.88/0.98                [c_7326,c_4203,c_5091,c_5092]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_7328,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) = sK6
% 3.88/0.98      | m1_subset_1(sK5,k1_zfmisc_1(sK2)) != iProver_top
% 3.88/0.98      | m1_subset_1(sK4,k1_zfmisc_1(sK2)) != iProver_top ),
% 3.88/0.98      inference(equality_resolution_simp,[status(thm)],[c_7327]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_22,negated_conjecture,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.88/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.88/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k2_partfun1(sK5,sK3,sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.88/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4682,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.88/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.88/0.98      | k2_partfun1(sK4,sK3,sK6,k9_subset_1(sK2,sK4,sK5)) != k7_relat_1(sK7,k9_subset_1(sK2,sK4,sK5)) ),
% 3.88/0.98      inference(demodulation,[status(thm)],[c_4679,c_22]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4683,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.88/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.88/0.98      | k2_partfun1(sK4,sK3,sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.88/0.98      inference(light_normalisation,[status(thm)],[c_4682,c_4203]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_4812,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.88/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.88/0.98      | k7_relat_1(sK6,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) ),
% 3.88/0.98      inference(demodulation,[status(thm)],[c_4683,c_4701]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6478,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.88/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.88/0.98      | k7_relat_1(sK6,k1_xboole_0) != k1_xboole_0 ),
% 3.88/0.98      inference(demodulation,[status(thm)],[c_5091,c_4812]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6479,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.88/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6
% 3.88/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 3.88/0.98      inference(light_normalisation,[status(thm)],[c_6478,c_5092]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_6480,plain,
% 3.88/0.98      ( k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK5) != sK7
% 3.88/0.98      | k2_partfun1(k4_subset_1(sK2,sK4,sK5),sK3,k1_tmap_1(sK2,sK3,sK4,sK5,sK6,sK7),sK4) != sK6 ),
% 3.88/0.98      inference(equality_resolution_simp,[status(thm)],[c_6479]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_41,plain,
% 3.88/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_32,negated_conjecture,
% 3.88/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 3.88/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(c_39,plain,
% 3.88/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.88/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.88/0.98  
% 3.88/0.98  cnf(contradiction,plain,
% 3.88/0.98      ( $false ),
% 3.88/0.98      inference(minisat,[status(thm)],[c_7419,c_7328,c_6480,c_41,c_39]) ).
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/0.98  
% 3.88/0.98  ------                               Statistics
% 3.88/0.98  
% 3.88/0.98  ------ General
% 3.88/0.98  
% 3.88/0.98  abstr_ref_over_cycles:                  0
% 3.88/0.98  abstr_ref_under_cycles:                 0
% 3.88/0.98  gc_basic_clause_elim:                   0
% 3.88/0.98  forced_gc_time:                         0
% 3.88/0.98  parsing_time:                           0.011
% 3.88/0.98  unif_index_cands_time:                  0.
% 3.88/0.98  unif_index_add_time:                    0.
% 3.88/0.98  orderings_time:                         0.
% 3.88/0.98  out_proof_time:                         0.017
% 3.88/0.98  total_time:                             0.44
% 3.88/0.98  num_of_symbols:                         57
% 3.88/0.98  num_of_terms:                           20370
% 3.88/0.98  
% 3.88/0.98  ------ Preprocessing
% 3.88/0.98  
% 3.88/0.98  num_of_splits:                          0
% 3.88/0.98  num_of_split_atoms:                     0
% 3.88/0.98  num_of_reused_defs:                     0
% 3.88/0.98  num_eq_ax_congr_red:                    28
% 3.88/0.98  num_of_sem_filtered_clauses:            1
% 3.88/0.98  num_of_subtypes:                        0
% 3.88/0.98  monotx_restored_types:                  0
% 3.88/0.98  sat_num_of_epr_types:                   0
% 3.88/0.98  sat_num_of_non_cyclic_types:            0
% 3.88/0.98  sat_guarded_non_collapsed_types:        0
% 3.88/0.98  num_pure_diseq_elim:                    0
% 3.88/0.98  simp_replaced_by:                       0
% 3.88/0.98  res_preprocessed:                       169
% 3.88/0.98  prep_upred:                             0
% 3.88/0.98  prep_unflattend:                        80
% 3.88/0.98  smt_new_axioms:                         0
% 3.88/0.98  pred_elim_cands:                        7
% 3.88/0.98  pred_elim:                              1
% 3.88/0.98  pred_elim_cl:                           2
% 3.88/0.98  pred_elim_cycles:                       5
% 3.88/0.98  merged_defs:                            8
% 3.88/0.98  merged_defs_ncl:                        0
% 3.88/0.98  bin_hyper_res:                          8
% 3.88/0.98  prep_cycles:                            4
% 3.88/0.98  pred_elim_time:                         0.01
% 3.88/0.98  splitting_time:                         0.
% 3.88/0.98  sem_filter_time:                        0.
% 3.88/0.98  monotx_time:                            0.001
% 3.88/0.98  subtype_inf_time:                       0.
% 3.88/0.98  
% 3.88/0.98  ------ Problem properties
% 3.88/0.98  
% 3.88/0.98  clauses:                                34
% 3.88/0.98  conjectures:                            13
% 3.88/0.98  epr:                                    11
% 3.88/0.98  horn:                                   25
% 3.88/0.98  ground:                                 14
% 3.88/0.98  unary:                                  15
% 3.88/0.98  binary:                                 8
% 3.88/0.98  lits:                                   130
% 3.88/0.98  lits_eq:                                15
% 3.88/0.98  fd_pure:                                0
% 3.88/0.98  fd_pseudo:                              0
% 3.88/0.98  fd_cond:                                0
% 3.88/0.98  fd_pseudo_cond:                         0
% 3.88/0.98  ac_symbols:                             0
% 3.88/0.98  
% 3.88/0.98  ------ Propositional Solver
% 3.88/0.98  
% 3.88/0.98  prop_solver_calls:                      28
% 3.88/0.98  prop_fast_solver_calls:                 1752
% 3.88/0.98  smt_solver_calls:                       0
% 3.88/0.98  smt_fast_solver_calls:                  0
% 3.88/0.98  prop_num_of_clauses:                    3572
% 3.88/0.98  prop_preprocess_simplified:             9244
% 3.88/0.98  prop_fo_subsumed:                       41
% 3.88/0.98  prop_solver_time:                       0.
% 3.88/0.98  smt_solver_time:                        0.
% 3.88/0.98  smt_fast_solver_time:                   0.
% 3.88/0.98  prop_fast_solver_time:                  0.
% 3.88/0.98  prop_unsat_core_time:                   0.
% 3.88/0.98  
% 3.88/0.98  ------ QBF
% 3.88/0.98  
% 3.88/0.98  qbf_q_res:                              0
% 3.88/0.98  qbf_num_tautologies:                    0
% 3.88/0.98  qbf_prep_cycles:                        0
% 3.88/0.98  
% 3.88/0.98  ------ BMC1
% 3.88/0.98  
% 3.88/0.98  bmc1_current_bound:                     -1
% 3.88/0.98  bmc1_last_solved_bound:                 -1
% 3.88/0.98  bmc1_unsat_core_size:                   -1
% 3.88/0.98  bmc1_unsat_core_parents_size:           -1
% 3.88/0.98  bmc1_merge_next_fun:                    0
% 3.88/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.88/0.98  
% 3.88/0.98  ------ Instantiation
% 3.88/0.98  
% 3.88/0.98  inst_num_of_clauses:                    800
% 3.88/0.98  inst_num_in_passive:                    304
% 3.88/0.98  inst_num_in_active:                     375
% 3.88/0.98  inst_num_in_unprocessed:                121
% 3.88/0.98  inst_num_of_loops:                      490
% 3.88/0.98  inst_num_of_learning_restarts:          0
% 3.88/0.98  inst_num_moves_active_passive:          113
% 3.88/0.98  inst_lit_activity:                      0
% 3.88/0.98  inst_lit_activity_moves:                1
% 3.88/0.98  inst_num_tautologies:                   0
% 3.88/0.98  inst_num_prop_implied:                  0
% 3.88/0.98  inst_num_existing_simplified:           0
% 3.88/0.98  inst_num_eq_res_simplified:             0
% 3.88/0.98  inst_num_child_elim:                    0
% 3.88/0.98  inst_num_of_dismatching_blockings:      123
% 3.88/0.98  inst_num_of_non_proper_insts:           731
% 3.88/0.98  inst_num_of_duplicates:                 0
% 3.88/0.98  inst_inst_num_from_inst_to_res:         0
% 3.88/0.98  inst_dismatching_checking_time:         0.
% 3.88/0.98  
% 3.88/0.98  ------ Resolution
% 3.88/0.98  
% 3.88/0.98  res_num_of_clauses:                     0
% 3.88/0.98  res_num_in_passive:                     0
% 3.88/0.98  res_num_in_active:                      0
% 3.88/0.98  res_num_of_loops:                       173
% 3.88/0.98  res_forward_subset_subsumed:            14
% 3.88/0.98  res_backward_subset_subsumed:           0
% 3.88/0.98  res_forward_subsumed:                   0
% 3.88/0.98  res_backward_subsumed:                  0
% 3.88/0.98  res_forward_subsumption_resolution:     0
% 3.88/0.98  res_backward_subsumption_resolution:    0
% 3.88/0.98  res_clause_to_clause_subsumption:       553
% 3.88/0.98  res_orphan_elimination:                 0
% 3.88/0.98  res_tautology_del:                      24
% 3.88/0.98  res_num_eq_res_simplified:              0
% 3.88/0.98  res_num_sel_changes:                    0
% 3.88/0.98  res_moves_from_active_to_pass:          0
% 3.88/0.98  
% 3.88/0.98  ------ Superposition
% 3.88/0.98  
% 3.88/0.98  sup_time_total:                         0.
% 3.88/0.98  sup_time_generating:                    0.
% 3.88/0.98  sup_time_sim_full:                      0.
% 3.88/0.98  sup_time_sim_immed:                     0.
% 3.88/0.98  
% 3.88/0.98  sup_num_of_clauses:                     186
% 3.88/0.98  sup_num_in_active:                      95
% 3.88/0.98  sup_num_in_passive:                     91
% 3.88/0.98  sup_num_of_loops:                       97
% 3.88/0.98  sup_fw_superposition:                   154
% 3.88/0.98  sup_bw_superposition:                   114
% 3.88/0.98  sup_immediate_simplified:               111
% 3.88/0.98  sup_given_eliminated:                   0
% 3.88/0.98  comparisons_done:                       0
% 3.88/0.98  comparisons_avoided:                    0
% 3.88/0.98  
% 3.88/0.98  ------ Simplifications
% 3.88/0.98  
% 3.88/0.98  
% 3.88/0.98  sim_fw_subset_subsumed:                 21
% 3.88/0.98  sim_bw_subset_subsumed:                 1
% 3.88/0.98  sim_fw_subsumed:                        41
% 3.88/0.98  sim_bw_subsumed:                        0
% 3.88/0.98  sim_fw_subsumption_res:                 0
% 3.88/0.98  sim_bw_subsumption_res:                 0
% 3.88/0.98  sim_tautology_del:                      9
% 3.88/0.98  sim_eq_tautology_del:                   3
% 3.88/0.98  sim_eq_res_simp:                        3
% 3.88/0.98  sim_fw_demodulated:                     41
% 3.88/0.98  sim_bw_demodulated:                     3
% 3.88/0.98  sim_light_normalised:                   38
% 3.88/0.98  sim_joinable_taut:                      0
% 3.88/0.98  sim_joinable_simp:                      0
% 3.88/0.98  sim_ac_normalised:                      0
% 3.88/0.98  sim_smt_subsumption:                    0
% 3.88/0.98  
%------------------------------------------------------------------------------
