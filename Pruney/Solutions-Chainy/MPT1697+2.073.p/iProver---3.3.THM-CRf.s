%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:39 EST 2020

% Result     : Theorem 5.94s
% Output     : CNFRefutation 5.94s
% Verified   : 
% Statistics : Number of formulae       :  181 (2099 expanded)
%              Number of clauses        :  120 ( 506 expanded)
%              Number of leaves         :   15 ( 857 expanded)
%              Depth                    :   23
%              Number of atoms          : 1137 (28803 expanded)
%              Number of equality atoms :  470 (6895 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f33,plain,(
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

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f23,f33,f32,f31,f30,f29,f28])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
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
    inference(equality_resolution,[],[f44])).

fof(f8,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f60,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f66,plain,(
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
    inference(equality_resolution,[],[f43])).

fof(f62,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_553,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_970,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_553])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_566,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
    | k9_subset_1(X1_50,X2_50,X0_50) = k3_xboole_0(X2_50,X0_50) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_958,plain,
    ( k9_subset_1(X0_50,X1_50,X2_50) = k3_xboole_0(X1_50,X2_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_566])).

cnf(c_2022,plain,
    ( k9_subset_1(sK0,X0_50,sK3) = k3_xboole_0(X0_50,sK3) ),
    inference(superposition,[status(thm)],[c_970,c_958])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_556,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_967,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_565,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | k2_partfun1(X1_50,X2_50,X0_50,X3_50) = k7_relat_1(X0_50,X3_50) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_959,plain,
    ( k2_partfun1(X0_50,X1_50,X2_50,X3_50) = k7_relat_1(X2_50,X3_50)
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_2129,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_959])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1321,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_50,X1_50,sK4,X2_50) = k7_relat_1(sK4,X2_50) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_1451,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50) ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_2749,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2129,c_20,c_18,c_1451])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_559,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_964,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_2128,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_959])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1316,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_50,X1_50,sK5,X2_50) = k7_relat_1(sK5,X2_50) ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_1446,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50) ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_2669,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2128,c_17,c_15,c_1446])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f65])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f47])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f48])).

cnf(c_159,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_13,c_12,c_11])).

cnf(c_160,plain,
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
    inference(renaming,[status(thm)],[c_159])).

cnf(c_546,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X4_50,X2_50)
    | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | v1_xboole_0(X1_50)
    | v1_xboole_0(X2_50)
    | v1_xboole_0(X4_50)
    | v1_xboole_0(X5_50)
    | k2_partfun1(X1_50,X2_50,X0_50,k9_subset_1(X5_50,X4_50,X1_50)) != k2_partfun1(X4_50,X2_50,X3_50,k9_subset_1(X5_50,X4_50,X1_50))
    | k2_partfun1(k4_subset_1(X5_50,X4_50,X1_50),X2_50,k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),X1_50) = X0_50 ),
    inference(subtyping,[status(esa)],[c_160])).

cnf(c_977,plain,
    ( k2_partfun1(X0_50,X1_50,X2_50,k9_subset_1(X3_50,X4_50,X0_50)) != k2_partfun1(X4_50,X1_50,X5_50,k9_subset_1(X3_50,X4_50,X0_50))
    | k2_partfun1(k4_subset_1(X3_50,X4_50,X0_50),X1_50,k1_tmap_1(X3_50,X1_50,X4_50,X0_50,X5_50,X2_50),X0_50) = X2_50
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | v1_funct_2(X5_50,X4_50,X1_50) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(X3_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X3_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_xboole_0(X3_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X4_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_4689,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_977])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_32,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_38,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_39,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_40,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13559,plain,
    ( v1_funct_1(X1_50) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
    | k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4689,c_29,c_32,c_38,c_39,c_40])).

cnf(c_13560,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_13559])).

cnf(c_13575,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2749,c_13560])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_30,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_36,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13779,plain,
    ( v1_xboole_0(X0_50) = iProver_top
    | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13575,c_30,c_35,c_36,c_37])).

cnf(c_13780,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_13779])).

cnf(c_13790,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2022,c_13780])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_206,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_381,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_382,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_384,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_25,c_23])).

cnf(c_395,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_206,c_384])).

cnf(c_396,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_544,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_396])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_3])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | k7_relat_1(X0_50,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_366])).

cnf(c_978,plain,
    ( k7_relat_1(X0_50,k1_xboole_0) = k1_xboole_0
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_1669,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_964,c_978])).

cnf(c_13791,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13790,c_544,c_1669])).

cnf(c_563,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X4_50,X2_50)
    | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
    | m1_subset_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_50,X4_50,X1_50),X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | v1_xboole_0(X1_50)
    | v1_xboole_0(X2_50)
    | v1_xboole_0(X4_50)
    | v1_xboole_0(X5_50) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_961,plain,
    ( v1_funct_2(X0_50,X1_50,X2_50) != iProver_top
    | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(X5_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X5_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_50,X4_50,X1_50),X2_50))) = iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X3_50) != iProver_top
    | v1_xboole_0(X5_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X4_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_563])).

cnf(c_2253,plain,
    ( k2_partfun1(k4_subset_1(X0_50,X1_50,X2_50),X3_50,k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50) = k7_relat_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50)
    | v1_funct_2(X5_50,X2_50,X3_50) != iProver_top
    | v1_funct_2(X4_50,X1_50,X3_50) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X3_50))) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_funct_1(X4_50) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50)) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X3_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_959])).

cnf(c_561,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X4_50,X2_50)
    | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | v1_funct_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50))
    | v1_xboole_0(X1_50)
    | v1_xboole_0(X2_50)
    | v1_xboole_0(X4_50)
    | v1_xboole_0(X5_50) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_963,plain,
    ( v1_funct_2(X0_50,X1_50,X2_50) != iProver_top
    | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(X5_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X5_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
    | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
    | v1_funct_1(X0_50) != iProver_top
    | v1_funct_1(X3_50) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50)) = iProver_top
    | v1_xboole_0(X5_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X4_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_561])).

cnf(c_6514,plain,
    ( k2_partfun1(k4_subset_1(X0_50,X1_50,X2_50),X3_50,k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50) = k7_relat_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50)
    | v1_funct_2(X5_50,X2_50,X3_50) != iProver_top
    | v1_funct_2(X4_50,X1_50,X3_50) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X3_50))) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_funct_1(X4_50) != iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X3_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2253,c_963])).

cnf(c_6518,plain,
    ( k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
    | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_964,c_6514])).

cnf(c_6787,plain,
    ( v1_funct_1(X2_50) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
    | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6518,c_29,c_32,c_38,c_39])).

cnf(c_6788,plain,
    ( k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
    | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_6787])).

cnf(c_6802,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_6788])).

cnf(c_7247,plain,
    ( v1_xboole_0(X0_50) = iProver_top
    | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6802,c_30,c_35,c_36])).

cnf(c_7248,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_7247])).

cnf(c_7257,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_970,c_7248])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_28,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_31,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7492,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7257,c_28,c_31])).

cnf(c_13792,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13791,c_2022,c_7492])).

cnf(c_1670,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_967,c_978])).

cnf(c_13793,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13792,c_544,c_1670])).

cnf(c_13794,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_13793])).

cnf(c_10,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_152,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_13,c_12,c_11])).

cnf(c_153,plain,
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
    inference(renaming,[status(thm)],[c_152])).

cnf(c_547,plain,
    ( ~ v1_funct_2(X0_50,X1_50,X2_50)
    | ~ v1_funct_2(X3_50,X4_50,X2_50)
    | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
    | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
    | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
    | ~ v1_funct_1(X0_50)
    | ~ v1_funct_1(X3_50)
    | v1_xboole_0(X1_50)
    | v1_xboole_0(X2_50)
    | v1_xboole_0(X4_50)
    | v1_xboole_0(X5_50)
    | k2_partfun1(X1_50,X2_50,X0_50,k9_subset_1(X5_50,X4_50,X1_50)) != k2_partfun1(X4_50,X2_50,X3_50,k9_subset_1(X5_50,X4_50,X1_50))
    | k2_partfun1(k4_subset_1(X5_50,X4_50,X1_50),X2_50,k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),X4_50) = X3_50 ),
    inference(subtyping,[status(esa)],[c_153])).

cnf(c_976,plain,
    ( k2_partfun1(X0_50,X1_50,X2_50,k9_subset_1(X3_50,X4_50,X0_50)) != k2_partfun1(X4_50,X1_50,X5_50,k9_subset_1(X3_50,X4_50,X0_50))
    | k2_partfun1(k4_subset_1(X3_50,X4_50,X0_50),X1_50,k1_tmap_1(X3_50,X1_50,X4_50,X0_50,X5_50,X2_50),X4_50) = X5_50
    | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
    | v1_funct_2(X5_50,X4_50,X1_50) != iProver_top
    | m1_subset_1(X4_50,k1_zfmisc_1(X3_50)) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X3_50)) != iProver_top
    | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
    | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50))) != iProver_top
    | v1_funct_1(X2_50) != iProver_top
    | v1_funct_1(X5_50) != iProver_top
    | v1_xboole_0(X3_50) = iProver_top
    | v1_xboole_0(X1_50) = iProver_top
    | v1_xboole_0(X4_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_547])).

cnf(c_3158,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_976])).

cnf(c_4596,plain,
    ( v1_funct_1(X1_50) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
    | k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(X2_50) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3158,c_29,c_32,c_38,c_39,c_40])).

cnf(c_4597,plain,
    ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
    | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
    | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
    | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
    | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
    | v1_funct_1(X1_50) != iProver_top
    | v1_xboole_0(X2_50) = iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_4596])).

cnf(c_4612,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2749,c_4597])).

cnf(c_10555,plain,
    ( v1_xboole_0(X0_50) = iProver_top
    | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4612,c_30,c_35,c_36,c_37])).

cnf(c_10556,plain,
    ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
    | v1_xboole_0(X0_50) = iProver_top ),
    inference(renaming,[status(thm)],[c_10555])).

cnf(c_10566,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2022,c_10556])).

cnf(c_10567,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10566,c_544,c_1669])).

cnf(c_10568,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10567,c_2022,c_7492])).

cnf(c_10569,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10568,c_544,c_1670])).

cnf(c_10570,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10569])).

cnf(c_14,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_560,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2087,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2022,c_560])).

cnf(c_2088,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2087,c_544])).

cnf(c_2753,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2088,c_1669,c_1670,c_2669,c_2749])).

cnf(c_2754,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_2753])).

cnf(c_7496,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_7492,c_2754])).

cnf(c_7497,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_7496,c_7492])).

cnf(c_33,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13794,c_10570,c_7497,c_33,c_31,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n001.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 17:15:15 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.31  % Running in FOF mode
% 5.94/1.45  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.94/1.45  
% 5.94/1.45  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 5.94/1.45  
% 5.94/1.45  ------  iProver source info
% 5.94/1.45  
% 5.94/1.45  git: date: 2020-06-30 10:37:57 +0100
% 5.94/1.45  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 5.94/1.45  git: non_committed_changes: false
% 5.94/1.45  git: last_make_outside_of_git: false
% 5.94/1.45  
% 5.94/1.45  ------ 
% 5.94/1.45  
% 5.94/1.45  ------ Input Options
% 5.94/1.45  
% 5.94/1.45  --out_options                           all
% 5.94/1.45  --tptp_safe_out                         true
% 5.94/1.45  --problem_path                          ""
% 5.94/1.45  --include_path                          ""
% 5.94/1.45  --clausifier                            res/vclausify_rel
% 5.94/1.45  --clausifier_options                    --mode clausify
% 5.94/1.45  --stdin                                 false
% 5.94/1.45  --stats_out                             all
% 5.94/1.45  
% 5.94/1.45  ------ General Options
% 5.94/1.45  
% 5.94/1.45  --fof                                   false
% 5.94/1.45  --time_out_real                         305.
% 5.94/1.45  --time_out_virtual                      -1.
% 5.94/1.45  --symbol_type_check                     false
% 5.94/1.45  --clausify_out                          false
% 5.94/1.45  --sig_cnt_out                           false
% 5.94/1.45  --trig_cnt_out                          false
% 5.94/1.45  --trig_cnt_out_tolerance                1.
% 5.94/1.45  --trig_cnt_out_sk_spl                   false
% 5.94/1.45  --abstr_cl_out                          false
% 5.94/1.45  
% 5.94/1.45  ------ Global Options
% 5.94/1.45  
% 5.94/1.45  --schedule                              default
% 5.94/1.45  --add_important_lit                     false
% 5.94/1.45  --prop_solver_per_cl                    1000
% 5.94/1.45  --min_unsat_core                        false
% 5.94/1.45  --soft_assumptions                      false
% 5.94/1.45  --soft_lemma_size                       3
% 5.94/1.45  --prop_impl_unit_size                   0
% 5.94/1.45  --prop_impl_unit                        []
% 5.94/1.45  --share_sel_clauses                     true
% 5.94/1.45  --reset_solvers                         false
% 5.94/1.45  --bc_imp_inh                            [conj_cone]
% 5.94/1.45  --conj_cone_tolerance                   3.
% 5.94/1.45  --extra_neg_conj                        none
% 5.94/1.45  --large_theory_mode                     true
% 5.94/1.45  --prolific_symb_bound                   200
% 5.94/1.45  --lt_threshold                          2000
% 5.94/1.45  --clause_weak_htbl                      true
% 5.94/1.45  --gc_record_bc_elim                     false
% 5.94/1.45  
% 5.94/1.45  ------ Preprocessing Options
% 5.94/1.45  
% 5.94/1.45  --preprocessing_flag                    true
% 5.94/1.45  --time_out_prep_mult                    0.1
% 5.94/1.45  --splitting_mode                        input
% 5.94/1.45  --splitting_grd                         true
% 5.94/1.45  --splitting_cvd                         false
% 5.94/1.45  --splitting_cvd_svl                     false
% 5.94/1.45  --splitting_nvd                         32
% 5.94/1.45  --sub_typing                            true
% 5.94/1.45  --prep_gs_sim                           true
% 5.94/1.45  --prep_unflatten                        true
% 5.94/1.45  --prep_res_sim                          true
% 5.94/1.45  --prep_upred                            true
% 5.94/1.45  --prep_sem_filter                       exhaustive
% 5.94/1.45  --prep_sem_filter_out                   false
% 5.94/1.45  --pred_elim                             true
% 5.94/1.45  --res_sim_input                         true
% 5.94/1.45  --eq_ax_congr_red                       true
% 5.94/1.45  --pure_diseq_elim                       true
% 5.94/1.45  --brand_transform                       false
% 5.94/1.45  --non_eq_to_eq                          false
% 5.94/1.45  --prep_def_merge                        true
% 5.94/1.45  --prep_def_merge_prop_impl              false
% 5.94/1.45  --prep_def_merge_mbd                    true
% 5.94/1.45  --prep_def_merge_tr_red                 false
% 5.94/1.45  --prep_def_merge_tr_cl                  false
% 5.94/1.45  --smt_preprocessing                     true
% 5.94/1.45  --smt_ac_axioms                         fast
% 5.94/1.45  --preprocessed_out                      false
% 5.94/1.45  --preprocessed_stats                    false
% 5.94/1.45  
% 5.94/1.45  ------ Abstraction refinement Options
% 5.94/1.45  
% 5.94/1.45  --abstr_ref                             []
% 5.94/1.45  --abstr_ref_prep                        false
% 5.94/1.45  --abstr_ref_until_sat                   false
% 5.94/1.45  --abstr_ref_sig_restrict                funpre
% 5.94/1.45  --abstr_ref_af_restrict_to_split_sk     false
% 5.94/1.45  --abstr_ref_under                       []
% 5.94/1.45  
% 5.94/1.45  ------ SAT Options
% 5.94/1.45  
% 5.94/1.45  --sat_mode                              false
% 5.94/1.45  --sat_fm_restart_options                ""
% 5.94/1.45  --sat_gr_def                            false
% 5.94/1.45  --sat_epr_types                         true
% 5.94/1.45  --sat_non_cyclic_types                  false
% 5.94/1.45  --sat_finite_models                     false
% 5.94/1.45  --sat_fm_lemmas                         false
% 5.94/1.45  --sat_fm_prep                           false
% 5.94/1.45  --sat_fm_uc_incr                        true
% 5.94/1.45  --sat_out_model                         small
% 5.94/1.45  --sat_out_clauses                       false
% 5.94/1.45  
% 5.94/1.45  ------ QBF Options
% 5.94/1.45  
% 5.94/1.45  --qbf_mode                              false
% 5.94/1.45  --qbf_elim_univ                         false
% 5.94/1.45  --qbf_dom_inst                          none
% 5.94/1.45  --qbf_dom_pre_inst                      false
% 5.94/1.45  --qbf_sk_in                             false
% 5.94/1.45  --qbf_pred_elim                         true
% 5.94/1.45  --qbf_split                             512
% 5.94/1.45  
% 5.94/1.45  ------ BMC1 Options
% 5.94/1.45  
% 5.94/1.45  --bmc1_incremental                      false
% 5.94/1.45  --bmc1_axioms                           reachable_all
% 5.94/1.45  --bmc1_min_bound                        0
% 5.94/1.45  --bmc1_max_bound                        -1
% 5.94/1.45  --bmc1_max_bound_default                -1
% 5.94/1.45  --bmc1_symbol_reachability              true
% 5.94/1.45  --bmc1_property_lemmas                  false
% 5.94/1.45  --bmc1_k_induction                      false
% 5.94/1.45  --bmc1_non_equiv_states                 false
% 5.94/1.45  --bmc1_deadlock                         false
% 5.94/1.45  --bmc1_ucm                              false
% 5.94/1.45  --bmc1_add_unsat_core                   none
% 5.94/1.45  --bmc1_unsat_core_children              false
% 5.94/1.45  --bmc1_unsat_core_extrapolate_axioms    false
% 5.94/1.45  --bmc1_out_stat                         full
% 5.94/1.45  --bmc1_ground_init                      false
% 5.94/1.45  --bmc1_pre_inst_next_state              false
% 5.94/1.45  --bmc1_pre_inst_state                   false
% 5.94/1.45  --bmc1_pre_inst_reach_state             false
% 5.94/1.45  --bmc1_out_unsat_core                   false
% 5.94/1.45  --bmc1_aig_witness_out                  false
% 5.94/1.45  --bmc1_verbose                          false
% 5.94/1.45  --bmc1_dump_clauses_tptp                false
% 5.94/1.45  --bmc1_dump_unsat_core_tptp             false
% 5.94/1.45  --bmc1_dump_file                        -
% 5.94/1.45  --bmc1_ucm_expand_uc_limit              128
% 5.94/1.45  --bmc1_ucm_n_expand_iterations          6
% 5.94/1.45  --bmc1_ucm_extend_mode                  1
% 5.94/1.45  --bmc1_ucm_init_mode                    2
% 5.94/1.45  --bmc1_ucm_cone_mode                    none
% 5.94/1.45  --bmc1_ucm_reduced_relation_type        0
% 5.94/1.45  --bmc1_ucm_relax_model                  4
% 5.94/1.45  --bmc1_ucm_full_tr_after_sat            true
% 5.94/1.45  --bmc1_ucm_expand_neg_assumptions       false
% 5.94/1.45  --bmc1_ucm_layered_model                none
% 5.94/1.45  --bmc1_ucm_max_lemma_size               10
% 5.94/1.45  
% 5.94/1.45  ------ AIG Options
% 5.94/1.45  
% 5.94/1.45  --aig_mode                              false
% 5.94/1.45  
% 5.94/1.45  ------ Instantiation Options
% 5.94/1.45  
% 5.94/1.45  --instantiation_flag                    true
% 5.94/1.45  --inst_sos_flag                         false
% 5.94/1.45  --inst_sos_phase                        true
% 5.94/1.45  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 5.94/1.45  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 5.94/1.45  --inst_lit_sel_side                     num_symb
% 5.94/1.45  --inst_solver_per_active                1400
% 5.94/1.45  --inst_solver_calls_frac                1.
% 5.94/1.45  --inst_passive_queue_type               priority_queues
% 5.94/1.45  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 5.94/1.45  --inst_passive_queues_freq              [25;2]
% 5.94/1.45  --inst_dismatching                      true
% 5.94/1.45  --inst_eager_unprocessed_to_passive     true
% 5.94/1.45  --inst_prop_sim_given                   true
% 5.94/1.45  --inst_prop_sim_new                     false
% 5.94/1.45  --inst_subs_new                         false
% 5.94/1.45  --inst_eq_res_simp                      false
% 5.94/1.45  --inst_subs_given                       false
% 5.94/1.45  --inst_orphan_elimination               true
% 5.94/1.45  --inst_learning_loop_flag               true
% 5.94/1.45  --inst_learning_start                   3000
% 5.94/1.45  --inst_learning_factor                  2
% 5.94/1.45  --inst_start_prop_sim_after_learn       3
% 5.94/1.45  --inst_sel_renew                        solver
% 5.94/1.45  --inst_lit_activity_flag                true
% 5.94/1.45  --inst_restr_to_given                   false
% 5.94/1.45  --inst_activity_threshold               500
% 5.94/1.45  --inst_out_proof                        true
% 5.94/1.45  
% 5.94/1.45  ------ Resolution Options
% 5.94/1.45  
% 5.94/1.45  --resolution_flag                       true
% 5.94/1.45  --res_lit_sel                           adaptive
% 5.94/1.45  --res_lit_sel_side                      none
% 5.94/1.45  --res_ordering                          kbo
% 5.94/1.45  --res_to_prop_solver                    active
% 5.94/1.45  --res_prop_simpl_new                    false
% 5.94/1.45  --res_prop_simpl_given                  true
% 5.94/1.45  --res_passive_queue_type                priority_queues
% 5.94/1.45  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 5.94/1.45  --res_passive_queues_freq               [15;5]
% 5.94/1.45  --res_forward_subs                      full
% 5.94/1.45  --res_backward_subs                     full
% 5.94/1.45  --res_forward_subs_resolution           true
% 5.94/1.45  --res_backward_subs_resolution          true
% 5.94/1.45  --res_orphan_elimination                true
% 5.94/1.45  --res_time_limit                        2.
% 5.94/1.45  --res_out_proof                         true
% 5.94/1.45  
% 5.94/1.45  ------ Superposition Options
% 5.94/1.45  
% 5.94/1.45  --superposition_flag                    true
% 5.94/1.45  --sup_passive_queue_type                priority_queues
% 5.94/1.45  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 5.94/1.45  --sup_passive_queues_freq               [8;1;4]
% 5.94/1.45  --demod_completeness_check              fast
% 5.94/1.45  --demod_use_ground                      true
% 5.94/1.45  --sup_to_prop_solver                    passive
% 5.94/1.45  --sup_prop_simpl_new                    true
% 5.94/1.45  --sup_prop_simpl_given                  true
% 5.94/1.45  --sup_fun_splitting                     false
% 5.94/1.45  --sup_smt_interval                      50000
% 5.94/1.45  
% 5.94/1.45  ------ Superposition Simplification Setup
% 5.94/1.45  
% 5.94/1.45  --sup_indices_passive                   []
% 5.94/1.45  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.94/1.45  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.94/1.45  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.94/1.45  --sup_full_triv                         [TrivRules;PropSubs]
% 5.94/1.45  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.94/1.45  --sup_full_bw                           [BwDemod]
% 5.94/1.45  --sup_immed_triv                        [TrivRules]
% 5.94/1.45  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 5.94/1.45  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.94/1.45  --sup_immed_bw_main                     []
% 5.94/1.45  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.94/1.45  --sup_input_triv                        [Unflattening;TrivRules]
% 5.94/1.45  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.94/1.45  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.94/1.45  
% 5.94/1.45  ------ Combination Options
% 5.94/1.45  
% 5.94/1.45  --comb_res_mult                         3
% 5.94/1.45  --comb_sup_mult                         2
% 5.94/1.45  --comb_inst_mult                        10
% 5.94/1.45  
% 5.94/1.45  ------ Debug Options
% 5.94/1.45  
% 5.94/1.45  --dbg_backtrace                         false
% 5.94/1.45  --dbg_dump_prop_clauses                 false
% 5.94/1.45  --dbg_dump_prop_clauses_file            -
% 5.94/1.45  --dbg_out_stat                          false
% 5.94/1.45  ------ Parsing...
% 5.94/1.45  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 5.94/1.45  
% 5.94/1.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 5.94/1.45  
% 5.94/1.45  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 5.94/1.45  
% 5.94/1.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 5.94/1.45  ------ Proving...
% 5.94/1.45  ------ Problem Properties 
% 5.94/1.45  
% 5.94/1.45  
% 5.94/1.45  clauses                                 23
% 5.94/1.45  conjectures                             13
% 5.94/1.45  EPR                                     8
% 5.94/1.45  Horn                                    17
% 5.94/1.45  unary                                   13
% 5.94/1.45  binary                                  2
% 5.94/1.45  lits                                    107
% 5.94/1.45  lits eq                                 13
% 5.94/1.45  fd_pure                                 0
% 5.94/1.45  fd_pseudo                               0
% 5.94/1.45  fd_cond                                 0
% 5.94/1.45  fd_pseudo_cond                          0
% 5.94/1.45  AC symbols                              0
% 5.94/1.45  
% 5.94/1.45  ------ Schedule dynamic 5 is on 
% 5.94/1.45  
% 5.94/1.45  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 5.94/1.45  
% 5.94/1.45  
% 5.94/1.45  ------ 
% 5.94/1.45  Current options:
% 5.94/1.45  ------ 
% 5.94/1.45  
% 5.94/1.45  ------ Input Options
% 5.94/1.45  
% 5.94/1.45  --out_options                           all
% 5.94/1.45  --tptp_safe_out                         true
% 5.94/1.45  --problem_path                          ""
% 5.94/1.45  --include_path                          ""
% 5.94/1.45  --clausifier                            res/vclausify_rel
% 5.94/1.45  --clausifier_options                    --mode clausify
% 5.94/1.45  --stdin                                 false
% 5.94/1.45  --stats_out                             all
% 5.94/1.45  
% 5.94/1.45  ------ General Options
% 5.94/1.45  
% 5.94/1.45  --fof                                   false
% 5.94/1.45  --time_out_real                         305.
% 5.94/1.45  --time_out_virtual                      -1.
% 5.94/1.45  --symbol_type_check                     false
% 5.94/1.45  --clausify_out                          false
% 5.94/1.45  --sig_cnt_out                           false
% 5.94/1.45  --trig_cnt_out                          false
% 5.94/1.45  --trig_cnt_out_tolerance                1.
% 5.94/1.45  --trig_cnt_out_sk_spl                   false
% 5.94/1.45  --abstr_cl_out                          false
% 5.94/1.45  
% 5.94/1.45  ------ Global Options
% 5.94/1.45  
% 5.94/1.45  --schedule                              default
% 5.94/1.45  --add_important_lit                     false
% 5.94/1.45  --prop_solver_per_cl                    1000
% 5.94/1.45  --min_unsat_core                        false
% 5.94/1.45  --soft_assumptions                      false
% 5.94/1.45  --soft_lemma_size                       3
% 5.94/1.45  --prop_impl_unit_size                   0
% 5.94/1.45  --prop_impl_unit                        []
% 5.94/1.45  --share_sel_clauses                     true
% 5.94/1.45  --reset_solvers                         false
% 5.94/1.45  --bc_imp_inh                            [conj_cone]
% 5.94/1.45  --conj_cone_tolerance                   3.
% 5.94/1.45  --extra_neg_conj                        none
% 5.94/1.45  --large_theory_mode                     true
% 5.94/1.45  --prolific_symb_bound                   200
% 5.94/1.45  --lt_threshold                          2000
% 5.94/1.45  --clause_weak_htbl                      true
% 5.94/1.45  --gc_record_bc_elim                     false
% 5.94/1.45  
% 5.94/1.45  ------ Preprocessing Options
% 5.94/1.45  
% 5.94/1.45  --preprocessing_flag                    true
% 5.94/1.45  --time_out_prep_mult                    0.1
% 5.94/1.45  --splitting_mode                        input
% 5.94/1.45  --splitting_grd                         true
% 5.94/1.45  --splitting_cvd                         false
% 5.94/1.45  --splitting_cvd_svl                     false
% 5.94/1.45  --splitting_nvd                         32
% 5.94/1.45  --sub_typing                            true
% 5.94/1.45  --prep_gs_sim                           true
% 5.94/1.45  --prep_unflatten                        true
% 5.94/1.45  --prep_res_sim                          true
% 5.94/1.45  --prep_upred                            true
% 5.94/1.45  --prep_sem_filter                       exhaustive
% 5.94/1.45  --prep_sem_filter_out                   false
% 5.94/1.45  --pred_elim                             true
% 5.94/1.45  --res_sim_input                         true
% 5.94/1.45  --eq_ax_congr_red                       true
% 5.94/1.45  --pure_diseq_elim                       true
% 5.94/1.45  --brand_transform                       false
% 5.94/1.45  --non_eq_to_eq                          false
% 5.94/1.45  --prep_def_merge                        true
% 5.94/1.45  --prep_def_merge_prop_impl              false
% 5.94/1.45  --prep_def_merge_mbd                    true
% 5.94/1.45  --prep_def_merge_tr_red                 false
% 5.94/1.45  --prep_def_merge_tr_cl                  false
% 5.94/1.45  --smt_preprocessing                     true
% 5.94/1.45  --smt_ac_axioms                         fast
% 5.94/1.45  --preprocessed_out                      false
% 5.94/1.45  --preprocessed_stats                    false
% 5.94/1.45  
% 5.94/1.45  ------ Abstraction refinement Options
% 5.94/1.45  
% 5.94/1.45  --abstr_ref                             []
% 5.94/1.45  --abstr_ref_prep                        false
% 5.94/1.45  --abstr_ref_until_sat                   false
% 5.94/1.45  --abstr_ref_sig_restrict                funpre
% 5.94/1.45  --abstr_ref_af_restrict_to_split_sk     false
% 5.94/1.45  --abstr_ref_under                       []
% 5.94/1.45  
% 5.94/1.45  ------ SAT Options
% 5.94/1.45  
% 5.94/1.45  --sat_mode                              false
% 5.94/1.45  --sat_fm_restart_options                ""
% 5.94/1.45  --sat_gr_def                            false
% 5.94/1.45  --sat_epr_types                         true
% 5.94/1.45  --sat_non_cyclic_types                  false
% 5.94/1.45  --sat_finite_models                     false
% 5.94/1.45  --sat_fm_lemmas                         false
% 5.94/1.45  --sat_fm_prep                           false
% 5.94/1.45  --sat_fm_uc_incr                        true
% 5.94/1.45  --sat_out_model                         small
% 5.94/1.45  --sat_out_clauses                       false
% 5.94/1.45  
% 5.94/1.45  ------ QBF Options
% 5.94/1.45  
% 5.94/1.45  --qbf_mode                              false
% 5.94/1.45  --qbf_elim_univ                         false
% 5.94/1.45  --qbf_dom_inst                          none
% 5.94/1.45  --qbf_dom_pre_inst                      false
% 5.94/1.45  --qbf_sk_in                             false
% 5.94/1.45  --qbf_pred_elim                         true
% 5.94/1.45  --qbf_split                             512
% 5.94/1.45  
% 5.94/1.45  ------ BMC1 Options
% 5.94/1.45  
% 5.94/1.45  --bmc1_incremental                      false
% 5.94/1.45  --bmc1_axioms                           reachable_all
% 5.94/1.45  --bmc1_min_bound                        0
% 5.94/1.45  --bmc1_max_bound                        -1
% 5.94/1.45  --bmc1_max_bound_default                -1
% 5.94/1.45  --bmc1_symbol_reachability              true
% 5.94/1.45  --bmc1_property_lemmas                  false
% 5.94/1.45  --bmc1_k_induction                      false
% 5.94/1.45  --bmc1_non_equiv_states                 false
% 5.94/1.45  --bmc1_deadlock                         false
% 5.94/1.45  --bmc1_ucm                              false
% 5.94/1.45  --bmc1_add_unsat_core                   none
% 5.94/1.45  --bmc1_unsat_core_children              false
% 5.94/1.45  --bmc1_unsat_core_extrapolate_axioms    false
% 5.94/1.45  --bmc1_out_stat                         full
% 5.94/1.45  --bmc1_ground_init                      false
% 5.94/1.45  --bmc1_pre_inst_next_state              false
% 5.94/1.45  --bmc1_pre_inst_state                   false
% 5.94/1.45  --bmc1_pre_inst_reach_state             false
% 5.94/1.45  --bmc1_out_unsat_core                   false
% 5.94/1.45  --bmc1_aig_witness_out                  false
% 5.94/1.45  --bmc1_verbose                          false
% 5.94/1.45  --bmc1_dump_clauses_tptp                false
% 5.94/1.45  --bmc1_dump_unsat_core_tptp             false
% 5.94/1.45  --bmc1_dump_file                        -
% 5.94/1.45  --bmc1_ucm_expand_uc_limit              128
% 5.94/1.45  --bmc1_ucm_n_expand_iterations          6
% 5.94/1.45  --bmc1_ucm_extend_mode                  1
% 5.94/1.45  --bmc1_ucm_init_mode                    2
% 5.94/1.45  --bmc1_ucm_cone_mode                    none
% 5.94/1.45  --bmc1_ucm_reduced_relation_type        0
% 5.94/1.45  --bmc1_ucm_relax_model                  4
% 5.94/1.45  --bmc1_ucm_full_tr_after_sat            true
% 5.94/1.45  --bmc1_ucm_expand_neg_assumptions       false
% 5.94/1.45  --bmc1_ucm_layered_model                none
% 5.94/1.45  --bmc1_ucm_max_lemma_size               10
% 5.94/1.45  
% 5.94/1.45  ------ AIG Options
% 5.94/1.45  
% 5.94/1.45  --aig_mode                              false
% 5.94/1.45  
% 5.94/1.45  ------ Instantiation Options
% 5.94/1.45  
% 5.94/1.45  --instantiation_flag                    true
% 5.94/1.45  --inst_sos_flag                         false
% 5.94/1.45  --inst_sos_phase                        true
% 5.94/1.45  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 5.94/1.45  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 5.94/1.45  --inst_lit_sel_side                     none
% 5.94/1.45  --inst_solver_per_active                1400
% 5.94/1.45  --inst_solver_calls_frac                1.
% 5.94/1.45  --inst_passive_queue_type               priority_queues
% 5.94/1.45  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 5.94/1.45  --inst_passive_queues_freq              [25;2]
% 5.94/1.45  --inst_dismatching                      true
% 5.94/1.45  --inst_eager_unprocessed_to_passive     true
% 5.94/1.45  --inst_prop_sim_given                   true
% 5.94/1.45  --inst_prop_sim_new                     false
% 5.94/1.45  --inst_subs_new                         false
% 5.94/1.45  --inst_eq_res_simp                      false
% 5.94/1.45  --inst_subs_given                       false
% 5.94/1.45  --inst_orphan_elimination               true
% 5.94/1.45  --inst_learning_loop_flag               true
% 5.94/1.45  --inst_learning_start                   3000
% 5.94/1.45  --inst_learning_factor                  2
% 5.94/1.45  --inst_start_prop_sim_after_learn       3
% 5.94/1.45  --inst_sel_renew                        solver
% 5.94/1.45  --inst_lit_activity_flag                true
% 5.94/1.45  --inst_restr_to_given                   false
% 5.94/1.45  --inst_activity_threshold               500
% 5.94/1.45  --inst_out_proof                        true
% 5.94/1.45  
% 5.94/1.45  ------ Resolution Options
% 5.94/1.45  
% 5.94/1.45  --resolution_flag                       false
% 5.94/1.45  --res_lit_sel                           adaptive
% 5.94/1.45  --res_lit_sel_side                      none
% 5.94/1.45  --res_ordering                          kbo
% 5.94/1.45  --res_to_prop_solver                    active
% 5.94/1.45  --res_prop_simpl_new                    false
% 5.94/1.45  --res_prop_simpl_given                  true
% 5.94/1.45  --res_passive_queue_type                priority_queues
% 5.94/1.45  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 5.94/1.45  --res_passive_queues_freq               [15;5]
% 5.94/1.45  --res_forward_subs                      full
% 5.94/1.45  --res_backward_subs                     full
% 5.94/1.45  --res_forward_subs_resolution           true
% 5.94/1.45  --res_backward_subs_resolution          true
% 5.94/1.45  --res_orphan_elimination                true
% 5.94/1.45  --res_time_limit                        2.
% 5.94/1.45  --res_out_proof                         true
% 5.94/1.45  
% 5.94/1.45  ------ Superposition Options
% 5.94/1.45  
% 5.94/1.45  --superposition_flag                    true
% 5.94/1.45  --sup_passive_queue_type                priority_queues
% 5.94/1.45  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 5.94/1.45  --sup_passive_queues_freq               [8;1;4]
% 5.94/1.45  --demod_completeness_check              fast
% 5.94/1.45  --demod_use_ground                      true
% 5.94/1.45  --sup_to_prop_solver                    passive
% 5.94/1.45  --sup_prop_simpl_new                    true
% 5.94/1.45  --sup_prop_simpl_given                  true
% 5.94/1.45  --sup_fun_splitting                     false
% 5.94/1.45  --sup_smt_interval                      50000
% 5.94/1.45  
% 5.94/1.45  ------ Superposition Simplification Setup
% 5.94/1.45  
% 5.94/1.45  --sup_indices_passive                   []
% 5.94/1.45  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.94/1.45  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.94/1.45  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 5.94/1.45  --sup_full_triv                         [TrivRules;PropSubs]
% 5.94/1.45  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.94/1.45  --sup_full_bw                           [BwDemod]
% 5.94/1.45  --sup_immed_triv                        [TrivRules]
% 5.94/1.45  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 5.94/1.45  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.94/1.45  --sup_immed_bw_main                     []
% 5.94/1.45  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.94/1.45  --sup_input_triv                        [Unflattening;TrivRules]
% 5.94/1.45  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 5.94/1.45  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 5.94/1.45  
% 5.94/1.45  ------ Combination Options
% 5.94/1.45  
% 5.94/1.45  --comb_res_mult                         3
% 5.94/1.45  --comb_sup_mult                         2
% 5.94/1.45  --comb_inst_mult                        10
% 5.94/1.45  
% 5.94/1.45  ------ Debug Options
% 5.94/1.45  
% 5.94/1.45  --dbg_backtrace                         false
% 5.94/1.45  --dbg_dump_prop_clauses                 false
% 5.94/1.45  --dbg_dump_prop_clauses_file            -
% 5.94/1.45  --dbg_out_stat                          false
% 5.94/1.45  
% 5.94/1.45  
% 5.94/1.45  
% 5.94/1.45  
% 5.94/1.45  ------ Proving...
% 5.94/1.45  
% 5.94/1.45  
% 5.94/1.45  % SZS status Theorem for theBenchmark.p
% 5.94/1.45  
% 5.94/1.45  % SZS output start CNFRefutation for theBenchmark.p
% 5.94/1.45  
% 5.94/1.45  fof(f9,conjecture,(
% 5.94/1.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 5.94/1.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.94/1.45  
% 5.94/1.45  fof(f10,negated_conjecture,(
% 5.94/1.45    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 5.94/1.45    inference(negated_conjecture,[],[f9])).
% 5.94/1.45  
% 5.94/1.45  fof(f22,plain,(
% 5.94/1.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 5.94/1.45    inference(ennf_transformation,[],[f10])).
% 5.94/1.45  
% 5.94/1.45  fof(f23,plain,(
% 5.94/1.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 5.94/1.45    inference(flattening,[],[f22])).
% 5.94/1.45  
% 5.94/1.45  fof(f33,plain,(
% 5.94/1.45    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 5.94/1.45    introduced(choice_axiom,[])).
% 5.94/1.45  
% 5.94/1.45  fof(f32,plain,(
% 5.94/1.45    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 5.94/1.45    introduced(choice_axiom,[])).
% 5.94/1.45  
% 5.94/1.45  fof(f31,plain,(
% 5.94/1.45    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 5.94/1.45    introduced(choice_axiom,[])).
% 5.94/1.45  
% 5.94/1.45  fof(f30,plain,(
% 5.94/1.45    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 5.94/1.45    introduced(choice_axiom,[])).
% 5.94/1.45  
% 5.94/1.45  fof(f29,plain,(
% 5.94/1.45    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 5.94/1.45    introduced(choice_axiom,[])).
% 5.94/1.45  
% 5.94/1.45  fof(f28,plain,(
% 5.94/1.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 5.94/1.45    introduced(choice_axiom,[])).
% 5.94/1.45  
% 5.94/1.45  fof(f34,plain,(
% 5.94/1.45    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 5.94/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f23,f33,f32,f31,f30,f29,f28])).
% 5.94/1.45  
% 5.94/1.45  fof(f54,plain,(
% 5.94/1.45    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f2,axiom,(
% 5.94/1.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 5.94/1.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.94/1.45  
% 5.94/1.45  fof(f11,plain,(
% 5.94/1.45    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 5.94/1.45    inference(ennf_transformation,[],[f2])).
% 5.94/1.45  
% 5.94/1.45  fof(f37,plain,(
% 5.94/1.45    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 5.94/1.45    inference(cnf_transformation,[],[f11])).
% 5.94/1.45  
% 5.94/1.45  fof(f58,plain,(
% 5.94/1.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f6,axiom,(
% 5.94/1.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 5.94/1.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.94/1.45  
% 5.94/1.45  fof(f16,plain,(
% 5.94/1.45    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 5.94/1.45    inference(ennf_transformation,[],[f6])).
% 5.94/1.45  
% 5.94/1.45  fof(f17,plain,(
% 5.94/1.45    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 5.94/1.45    inference(flattening,[],[f16])).
% 5.94/1.45  
% 5.94/1.45  fof(f42,plain,(
% 5.94/1.45    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 5.94/1.45    inference(cnf_transformation,[],[f17])).
% 5.94/1.45  
% 5.94/1.45  fof(f56,plain,(
% 5.94/1.45    v1_funct_1(sK4)),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f61,plain,(
% 5.94/1.45    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f59,plain,(
% 5.94/1.45    v1_funct_1(sK5)),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f7,axiom,(
% 5.94/1.45    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 5.94/1.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.94/1.45  
% 5.94/1.45  fof(f18,plain,(
% 5.94/1.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 5.94/1.45    inference(ennf_transformation,[],[f7])).
% 5.94/1.45  
% 5.94/1.45  fof(f19,plain,(
% 5.94/1.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 5.94/1.45    inference(flattening,[],[f18])).
% 5.94/1.45  
% 5.94/1.45  fof(f26,plain,(
% 5.94/1.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 5.94/1.45    inference(nnf_transformation,[],[f19])).
% 5.94/1.45  
% 5.94/1.45  fof(f27,plain,(
% 5.94/1.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 5.94/1.45    inference(flattening,[],[f26])).
% 5.94/1.45  
% 5.94/1.45  fof(f44,plain,(
% 5.94/1.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.94/1.45    inference(cnf_transformation,[],[f27])).
% 5.94/1.45  
% 5.94/1.45  fof(f65,plain,(
% 5.94/1.45    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.94/1.45    inference(equality_resolution,[],[f44])).
% 5.94/1.45  
% 5.94/1.45  fof(f8,axiom,(
% 5.94/1.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 5.94/1.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.94/1.45  
% 5.94/1.45  fof(f20,plain,(
% 5.94/1.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 5.94/1.45    inference(ennf_transformation,[],[f8])).
% 5.94/1.45  
% 5.94/1.45  fof(f21,plain,(
% 5.94/1.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 5.94/1.45    inference(flattening,[],[f20])).
% 5.94/1.45  
% 5.94/1.45  fof(f46,plain,(
% 5.94/1.45    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.94/1.45    inference(cnf_transformation,[],[f21])).
% 5.94/1.45  
% 5.94/1.45  fof(f47,plain,(
% 5.94/1.45    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.94/1.45    inference(cnf_transformation,[],[f21])).
% 5.94/1.45  
% 5.94/1.45  fof(f48,plain,(
% 5.94/1.45    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.94/1.45    inference(cnf_transformation,[],[f21])).
% 5.94/1.45  
% 5.94/1.45  fof(f50,plain,(
% 5.94/1.45    ~v1_xboole_0(sK1)),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f53,plain,(
% 5.94/1.45    ~v1_xboole_0(sK3)),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f60,plain,(
% 5.94/1.45    v1_funct_2(sK5,sK3,sK1)),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f51,plain,(
% 5.94/1.45    ~v1_xboole_0(sK2)),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f57,plain,(
% 5.94/1.45    v1_funct_2(sK4,sK2,sK1)),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f1,axiom,(
% 5.94/1.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 5.94/1.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.94/1.45  
% 5.94/1.45  fof(f24,plain,(
% 5.94/1.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 5.94/1.45    inference(nnf_transformation,[],[f1])).
% 5.94/1.45  
% 5.94/1.45  fof(f35,plain,(
% 5.94/1.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 5.94/1.45    inference(cnf_transformation,[],[f24])).
% 5.94/1.45  
% 5.94/1.45  fof(f4,axiom,(
% 5.94/1.45    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 5.94/1.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.94/1.45  
% 5.94/1.45  fof(f13,plain,(
% 5.94/1.45    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 5.94/1.45    inference(ennf_transformation,[],[f4])).
% 5.94/1.45  
% 5.94/1.45  fof(f14,plain,(
% 5.94/1.45    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 5.94/1.45    inference(flattening,[],[f13])).
% 5.94/1.45  
% 5.94/1.45  fof(f25,plain,(
% 5.94/1.45    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 5.94/1.45    inference(nnf_transformation,[],[f14])).
% 5.94/1.45  
% 5.94/1.45  fof(f39,plain,(
% 5.94/1.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.94/1.45    inference(cnf_transformation,[],[f25])).
% 5.94/1.45  
% 5.94/1.45  fof(f55,plain,(
% 5.94/1.45    r1_subset_1(sK2,sK3)),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f5,axiom,(
% 5.94/1.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 5.94/1.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.94/1.45  
% 5.94/1.45  fof(f15,plain,(
% 5.94/1.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.94/1.45    inference(ennf_transformation,[],[f5])).
% 5.94/1.45  
% 5.94/1.45  fof(f41,plain,(
% 5.94/1.45    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 5.94/1.45    inference(cnf_transformation,[],[f15])).
% 5.94/1.45  
% 5.94/1.45  fof(f3,axiom,(
% 5.94/1.45    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 5.94/1.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 5.94/1.45  
% 5.94/1.45  fof(f12,plain,(
% 5.94/1.45    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 5.94/1.45    inference(ennf_transformation,[],[f3])).
% 5.94/1.45  
% 5.94/1.45  fof(f38,plain,(
% 5.94/1.45    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 5.94/1.45    inference(cnf_transformation,[],[f12])).
% 5.94/1.45  
% 5.94/1.45  fof(f49,plain,(
% 5.94/1.45    ~v1_xboole_0(sK0)),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f52,plain,(
% 5.94/1.45    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  fof(f43,plain,(
% 5.94/1.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.94/1.45    inference(cnf_transformation,[],[f27])).
% 5.94/1.45  
% 5.94/1.45  fof(f66,plain,(
% 5.94/1.45    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 5.94/1.45    inference(equality_resolution,[],[f43])).
% 5.94/1.45  
% 5.94/1.45  fof(f62,plain,(
% 5.94/1.45    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 5.94/1.45    inference(cnf_transformation,[],[f34])).
% 5.94/1.45  
% 5.94/1.45  cnf(c_22,negated_conjecture,
% 5.94/1.45      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 5.94/1.45      inference(cnf_transformation,[],[f54]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_553,negated_conjecture,
% 5.94/1.45      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 5.94/1.45      inference(subtyping,[status(esa)],[c_22]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_970,plain,
% 5.94/1.45      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_553]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_2,plain,
% 5.94/1.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 5.94/1.45      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 5.94/1.45      inference(cnf_transformation,[],[f37]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_566,plain,
% 5.94/1.45      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(X1_50))
% 5.94/1.45      | k9_subset_1(X1_50,X2_50,X0_50) = k3_xboole_0(X2_50,X0_50) ),
% 5.94/1.45      inference(subtyping,[status(esa)],[c_2]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_958,plain,
% 5.94/1.45      ( k9_subset_1(X0_50,X1_50,X2_50) = k3_xboole_0(X1_50,X2_50)
% 5.94/1.45      | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_566]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_2022,plain,
% 5.94/1.45      ( k9_subset_1(sK0,X0_50,sK3) = k3_xboole_0(X0_50,sK3) ),
% 5.94/1.45      inference(superposition,[status(thm)],[c_970,c_958]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_18,negated_conjecture,
% 5.94/1.45      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 5.94/1.45      inference(cnf_transformation,[],[f58]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_556,negated_conjecture,
% 5.94/1.45      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 5.94/1.45      inference(subtyping,[status(esa)],[c_18]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_967,plain,
% 5.94/1.45      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_7,plain,
% 5.94/1.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.45      | ~ v1_funct_1(X0)
% 5.94/1.45      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 5.94/1.45      inference(cnf_transformation,[],[f42]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_565,plain,
% 5.94/1.45      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 5.94/1.45      | ~ v1_funct_1(X0_50)
% 5.94/1.45      | k2_partfun1(X1_50,X2_50,X0_50,X3_50) = k7_relat_1(X0_50,X3_50) ),
% 5.94/1.45      inference(subtyping,[status(esa)],[c_7]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_959,plain,
% 5.94/1.45      ( k2_partfun1(X0_50,X1_50,X2_50,X3_50) = k7_relat_1(X2_50,X3_50)
% 5.94/1.45      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 5.94/1.45      | v1_funct_1(X2_50) != iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_2129,plain,
% 5.94/1.45      ( k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50)
% 5.94/1.45      | v1_funct_1(sK4) != iProver_top ),
% 5.94/1.45      inference(superposition,[status(thm)],[c_967,c_959]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_20,negated_conjecture,
% 5.94/1.45      ( v1_funct_1(sK4) ),
% 5.94/1.45      inference(cnf_transformation,[],[f56]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_1321,plain,
% 5.94/1.45      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 5.94/1.45      | ~ v1_funct_1(sK4)
% 5.94/1.45      | k2_partfun1(X0_50,X1_50,sK4,X2_50) = k7_relat_1(sK4,X2_50) ),
% 5.94/1.45      inference(instantiation,[status(thm)],[c_565]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_1451,plain,
% 5.94/1.45      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 5.94/1.45      | ~ v1_funct_1(sK4)
% 5.94/1.45      | k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50) ),
% 5.94/1.45      inference(instantiation,[status(thm)],[c_1321]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_2749,plain,
% 5.94/1.45      ( k2_partfun1(sK2,sK1,sK4,X0_50) = k7_relat_1(sK4,X0_50) ),
% 5.94/1.45      inference(global_propositional_subsumption,
% 5.94/1.45                [status(thm)],
% 5.94/1.45                [c_2129,c_20,c_18,c_1451]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_15,negated_conjecture,
% 5.94/1.45      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 5.94/1.45      inference(cnf_transformation,[],[f61]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_559,negated_conjecture,
% 5.94/1.45      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 5.94/1.45      inference(subtyping,[status(esa)],[c_15]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_964,plain,
% 5.94/1.45      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_559]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_2128,plain,
% 5.94/1.45      ( k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50)
% 5.94/1.45      | v1_funct_1(sK5) != iProver_top ),
% 5.94/1.45      inference(superposition,[status(thm)],[c_964,c_959]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_17,negated_conjecture,
% 5.94/1.45      ( v1_funct_1(sK5) ),
% 5.94/1.45      inference(cnf_transformation,[],[f59]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_1316,plain,
% 5.94/1.45      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50)))
% 5.94/1.45      | ~ v1_funct_1(sK5)
% 5.94/1.45      | k2_partfun1(X0_50,X1_50,sK5,X2_50) = k7_relat_1(sK5,X2_50) ),
% 5.94/1.45      inference(instantiation,[status(thm)],[c_565]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_1446,plain,
% 5.94/1.45      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 5.94/1.45      | ~ v1_funct_1(sK5)
% 5.94/1.45      | k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50) ),
% 5.94/1.45      inference(instantiation,[status(thm)],[c_1316]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_2669,plain,
% 5.94/1.45      ( k2_partfun1(sK3,sK1,sK5,X0_50) = k7_relat_1(sK5,X0_50) ),
% 5.94/1.45      inference(global_propositional_subsumption,
% 5.94/1.45                [status(thm)],
% 5.94/1.45                [c_2128,c_17,c_15,c_1446]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_9,plain,
% 5.94/1.45      ( ~ v1_funct_2(X0,X1,X2)
% 5.94/1.45      | ~ v1_funct_2(X3,X4,X2)
% 5.94/1.45      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 5.94/1.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.94/1.45      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 5.94/1.45      | ~ v1_funct_1(X0)
% 5.94/1.45      | ~ v1_funct_1(X3)
% 5.94/1.45      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 5.94/1.45      | v1_xboole_0(X5)
% 5.94/1.45      | v1_xboole_0(X2)
% 5.94/1.45      | v1_xboole_0(X4)
% 5.94/1.45      | v1_xboole_0(X1)
% 5.94/1.45      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.94/1.45      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 5.94/1.45      inference(cnf_transformation,[],[f65]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_13,plain,
% 5.94/1.45      ( ~ v1_funct_2(X0,X1,X2)
% 5.94/1.45      | ~ v1_funct_2(X3,X4,X2)
% 5.94/1.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.94/1.45      | ~ v1_funct_1(X0)
% 5.94/1.45      | ~ v1_funct_1(X3)
% 5.94/1.45      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 5.94/1.45      | v1_xboole_0(X5)
% 5.94/1.45      | v1_xboole_0(X2)
% 5.94/1.45      | v1_xboole_0(X4)
% 5.94/1.45      | v1_xboole_0(X1) ),
% 5.94/1.45      inference(cnf_transformation,[],[f46]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_12,plain,
% 5.94/1.45      ( ~ v1_funct_2(X0,X1,X2)
% 5.94/1.45      | ~ v1_funct_2(X3,X4,X2)
% 5.94/1.45      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 5.94/1.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.94/1.45      | ~ v1_funct_1(X0)
% 5.94/1.45      | ~ v1_funct_1(X3)
% 5.94/1.45      | v1_xboole_0(X5)
% 5.94/1.45      | v1_xboole_0(X2)
% 5.94/1.45      | v1_xboole_0(X4)
% 5.94/1.45      | v1_xboole_0(X1) ),
% 5.94/1.45      inference(cnf_transformation,[],[f47]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_11,plain,
% 5.94/1.45      ( ~ v1_funct_2(X0,X1,X2)
% 5.94/1.45      | ~ v1_funct_2(X3,X4,X2)
% 5.94/1.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.94/1.45      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 5.94/1.45      | ~ v1_funct_1(X0)
% 5.94/1.45      | ~ v1_funct_1(X3)
% 5.94/1.45      | v1_xboole_0(X5)
% 5.94/1.45      | v1_xboole_0(X2)
% 5.94/1.45      | v1_xboole_0(X4)
% 5.94/1.45      | v1_xboole_0(X1) ),
% 5.94/1.45      inference(cnf_transformation,[],[f48]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_159,plain,
% 5.94/1.45      ( ~ v1_funct_1(X3)
% 5.94/1.45      | ~ v1_funct_1(X0)
% 5.94/1.45      | ~ v1_funct_2(X3,X4,X2)
% 5.94/1.45      | ~ v1_funct_2(X0,X1,X2)
% 5.94/1.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.94/1.45      | v1_xboole_0(X5)
% 5.94/1.45      | v1_xboole_0(X2)
% 5.94/1.45      | v1_xboole_0(X4)
% 5.94/1.45      | v1_xboole_0(X1)
% 5.94/1.45      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.94/1.45      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 5.94/1.45      inference(global_propositional_subsumption,
% 5.94/1.45                [status(thm)],
% 5.94/1.45                [c_9,c_13,c_12,c_11]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_160,plain,
% 5.94/1.45      ( ~ v1_funct_2(X0,X1,X2)
% 5.94/1.45      | ~ v1_funct_2(X3,X4,X2)
% 5.94/1.45      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.94/1.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.94/1.45      | ~ v1_funct_1(X0)
% 5.94/1.45      | ~ v1_funct_1(X3)
% 5.94/1.45      | v1_xboole_0(X1)
% 5.94/1.45      | v1_xboole_0(X2)
% 5.94/1.45      | v1_xboole_0(X4)
% 5.94/1.45      | v1_xboole_0(X5)
% 5.94/1.45      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.94/1.45      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 5.94/1.45      inference(renaming,[status(thm)],[c_159]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_546,plain,
% 5.94/1.45      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 5.94/1.45      | ~ v1_funct_2(X3_50,X4_50,X2_50)
% 5.94/1.45      | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
% 5.94/1.45      | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
% 5.94/1.45      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 5.94/1.45      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
% 5.94/1.45      | ~ v1_funct_1(X0_50)
% 5.94/1.45      | ~ v1_funct_1(X3_50)
% 5.94/1.45      | v1_xboole_0(X1_50)
% 5.94/1.45      | v1_xboole_0(X2_50)
% 5.94/1.45      | v1_xboole_0(X4_50)
% 5.94/1.45      | v1_xboole_0(X5_50)
% 5.94/1.45      | k2_partfun1(X1_50,X2_50,X0_50,k9_subset_1(X5_50,X4_50,X1_50)) != k2_partfun1(X4_50,X2_50,X3_50,k9_subset_1(X5_50,X4_50,X1_50))
% 5.94/1.45      | k2_partfun1(k4_subset_1(X5_50,X4_50,X1_50),X2_50,k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),X1_50) = X0_50 ),
% 5.94/1.45      inference(subtyping,[status(esa)],[c_160]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_977,plain,
% 5.94/1.45      ( k2_partfun1(X0_50,X1_50,X2_50,k9_subset_1(X3_50,X4_50,X0_50)) != k2_partfun1(X4_50,X1_50,X5_50,k9_subset_1(X3_50,X4_50,X0_50))
% 5.94/1.45      | k2_partfun1(k4_subset_1(X3_50,X4_50,X0_50),X1_50,k1_tmap_1(X3_50,X1_50,X4_50,X0_50,X5_50,X2_50),X0_50) = X2_50
% 5.94/1.45      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 5.94/1.45      | v1_funct_2(X5_50,X4_50,X1_50) != iProver_top
% 5.94/1.45      | m1_subset_1(X4_50,k1_zfmisc_1(X3_50)) != iProver_top
% 5.94/1.45      | m1_subset_1(X0_50,k1_zfmisc_1(X3_50)) != iProver_top
% 5.94/1.45      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 5.94/1.45      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50))) != iProver_top
% 5.94/1.45      | v1_funct_1(X2_50) != iProver_top
% 5.94/1.45      | v1_funct_1(X5_50) != iProver_top
% 5.94/1.45      | v1_xboole_0(X3_50) = iProver_top
% 5.94/1.45      | v1_xboole_0(X1_50) = iProver_top
% 5.94/1.45      | v1_xboole_0(X4_50) = iProver_top
% 5.94/1.45      | v1_xboole_0(X0_50) = iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_4689,plain,
% 5.94/1.45      ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 5.94/1.45      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
% 5.94/1.45      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 5.94/1.45      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 5.94/1.45      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.45      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 5.94/1.45      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 5.94/1.45      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.45      | v1_funct_1(X1_50) != iProver_top
% 5.94/1.45      | v1_funct_1(sK5) != iProver_top
% 5.94/1.45      | v1_xboole_0(X0_50) = iProver_top
% 5.94/1.45      | v1_xboole_0(X2_50) = iProver_top
% 5.94/1.45      | v1_xboole_0(sK1) = iProver_top
% 5.94/1.45      | v1_xboole_0(sK3) = iProver_top ),
% 5.94/1.45      inference(superposition,[status(thm)],[c_2669,c_977]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_26,negated_conjecture,
% 5.94/1.45      ( ~ v1_xboole_0(sK1) ),
% 5.94/1.45      inference(cnf_transformation,[],[f50]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_29,plain,
% 5.94/1.45      ( v1_xboole_0(sK1) != iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_23,negated_conjecture,
% 5.94/1.45      ( ~ v1_xboole_0(sK3) ),
% 5.94/1.45      inference(cnf_transformation,[],[f53]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_32,plain,
% 5.94/1.45      ( v1_xboole_0(sK3) != iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_38,plain,
% 5.94/1.45      ( v1_funct_1(sK5) = iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_16,negated_conjecture,
% 5.94/1.45      ( v1_funct_2(sK5,sK3,sK1) ),
% 5.94/1.45      inference(cnf_transformation,[],[f60]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_39,plain,
% 5.94/1.45      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_40,plain,
% 5.94/1.45      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_13559,plain,
% 5.94/1.45      ( v1_funct_1(X1_50) != iProver_top
% 5.94/1.45      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.45      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 5.94/1.45      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
% 5.94/1.45      | k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 5.94/1.45      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.45      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 5.94/1.45      | v1_xboole_0(X0_50) = iProver_top
% 5.94/1.45      | v1_xboole_0(X2_50) = iProver_top ),
% 5.94/1.45      inference(global_propositional_subsumption,
% 5.94/1.45                [status(thm)],
% 5.94/1.45                [c_4689,c_29,c_32,c_38,c_39,c_40]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_13560,plain,
% 5.94/1.45      ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 5.94/1.45      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),sK3) = sK5
% 5.94/1.45      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 5.94/1.45      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.45      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 5.94/1.45      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.45      | v1_funct_1(X1_50) != iProver_top
% 5.94/1.45      | v1_xboole_0(X2_50) = iProver_top
% 5.94/1.45      | v1_xboole_0(X0_50) = iProver_top ),
% 5.94/1.45      inference(renaming,[status(thm)],[c_13559]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_13575,plain,
% 5.94/1.45      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 5.94/1.45      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 5.94/1.45      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 5.94/1.45      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 5.94/1.45      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.45      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.45      | v1_funct_1(sK4) != iProver_top
% 5.94/1.45      | v1_xboole_0(X0_50) = iProver_top
% 5.94/1.45      | v1_xboole_0(sK2) = iProver_top ),
% 5.94/1.45      inference(superposition,[status(thm)],[c_2749,c_13560]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_25,negated_conjecture,
% 5.94/1.45      ( ~ v1_xboole_0(sK2) ),
% 5.94/1.45      inference(cnf_transformation,[],[f51]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_30,plain,
% 5.94/1.45      ( v1_xboole_0(sK2) != iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_35,plain,
% 5.94/1.45      ( v1_funct_1(sK4) = iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_19,negated_conjecture,
% 5.94/1.45      ( v1_funct_2(sK4,sK2,sK1) ),
% 5.94/1.45      inference(cnf_transformation,[],[f57]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_36,plain,
% 5.94/1.45      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_37,plain,
% 5.94/1.45      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_13779,plain,
% 5.94/1.45      ( v1_xboole_0(X0_50) = iProver_top
% 5.94/1.45      | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 5.94/1.45      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 5.94/1.45      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.45      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
% 5.94/1.45      inference(global_propositional_subsumption,
% 5.94/1.45                [status(thm)],
% 5.94/1.45                [c_13575,c_30,c_35,c_36,c_37]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_13780,plain,
% 5.94/1.45      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 5.94/1.45      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 5.94/1.45      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.45      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.45      | v1_xboole_0(X0_50) = iProver_top ),
% 5.94/1.45      inference(renaming,[status(thm)],[c_13779]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_13790,plain,
% 5.94/1.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 5.94/1.45      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 5.94/1.45      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.45      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.45      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.45      inference(superposition,[status(thm)],[c_2022,c_13780]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_1,plain,
% 5.94/1.45      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 5.94/1.45      inference(cnf_transformation,[],[f35]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_206,plain,
% 5.94/1.45      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 5.94/1.45      inference(prop_impl,[status(thm)],[c_1]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_5,plain,
% 5.94/1.45      ( ~ r1_subset_1(X0,X1)
% 5.94/1.45      | r1_xboole_0(X0,X1)
% 5.94/1.45      | v1_xboole_0(X0)
% 5.94/1.45      | v1_xboole_0(X1) ),
% 5.94/1.45      inference(cnf_transformation,[],[f39]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_21,negated_conjecture,
% 5.94/1.45      ( r1_subset_1(sK2,sK3) ),
% 5.94/1.45      inference(cnf_transformation,[],[f55]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_381,plain,
% 5.94/1.45      ( r1_xboole_0(X0,X1)
% 5.94/1.45      | v1_xboole_0(X0)
% 5.94/1.45      | v1_xboole_0(X1)
% 5.94/1.45      | sK3 != X1
% 5.94/1.45      | sK2 != X0 ),
% 5.94/1.45      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_382,plain,
% 5.94/1.45      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 5.94/1.45      inference(unflattening,[status(thm)],[c_381]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_384,plain,
% 5.94/1.45      ( r1_xboole_0(sK2,sK3) ),
% 5.94/1.45      inference(global_propositional_subsumption,
% 5.94/1.45                [status(thm)],
% 5.94/1.45                [c_382,c_25,c_23]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_395,plain,
% 5.94/1.45      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 5.94/1.45      inference(resolution_lifted,[status(thm)],[c_206,c_384]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_396,plain,
% 5.94/1.45      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 5.94/1.45      inference(unflattening,[status(thm)],[c_395]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_544,plain,
% 5.94/1.45      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 5.94/1.45      inference(subtyping,[status(esa)],[c_396]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_6,plain,
% 5.94/1.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.45      | v1_relat_1(X0) ),
% 5.94/1.45      inference(cnf_transformation,[],[f41]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_3,plain,
% 5.94/1.45      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 5.94/1.45      inference(cnf_transformation,[],[f38]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_366,plain,
% 5.94/1.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.45      | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 5.94/1.45      inference(resolution,[status(thm)],[c_6,c_3]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_545,plain,
% 5.94/1.45      ( ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 5.94/1.45      | k7_relat_1(X0_50,k1_xboole_0) = k1_xboole_0 ),
% 5.94/1.45      inference(subtyping,[status(esa)],[c_366]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_978,plain,
% 5.94/1.45      ( k7_relat_1(X0_50,k1_xboole_0) = k1_xboole_0
% 5.94/1.45      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top ),
% 5.94/1.45      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_1669,plain,
% 5.94/1.45      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 5.94/1.45      inference(superposition,[status(thm)],[c_964,c_978]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_13791,plain,
% 5.94/1.45      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 5.94/1.45      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 5.94/1.45      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.45      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.45      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.45      inference(light_normalisation,[status(thm)],[c_13790,c_544,c_1669]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_563,plain,
% 5.94/1.45      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 5.94/1.45      | ~ v1_funct_2(X3_50,X4_50,X2_50)
% 5.94/1.45      | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
% 5.94/1.45      | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
% 5.94/1.45      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 5.94/1.45      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
% 5.94/1.45      | m1_subset_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_50,X4_50,X1_50),X2_50)))
% 5.94/1.45      | ~ v1_funct_1(X0_50)
% 5.94/1.45      | ~ v1_funct_1(X3_50)
% 5.94/1.45      | v1_xboole_0(X1_50)
% 5.94/1.45      | v1_xboole_0(X2_50)
% 5.94/1.45      | v1_xboole_0(X4_50)
% 5.94/1.45      | v1_xboole_0(X5_50) ),
% 5.94/1.45      inference(subtyping,[status(esa)],[c_11]) ).
% 5.94/1.45  
% 5.94/1.45  cnf(c_961,plain,
% 5.94/1.45      ( v1_funct_2(X0_50,X1_50,X2_50) != iProver_top
% 5.94/1.45      | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
% 5.94/1.45      | m1_subset_1(X4_50,k1_zfmisc_1(X5_50)) != iProver_top
% 5.94/1.45      | m1_subset_1(X1_50,k1_zfmisc_1(X5_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 5.94/1.46      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
% 5.94/1.46      | m1_subset_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_50,X4_50,X1_50),X2_50))) = iProver_top
% 5.94/1.46      | v1_funct_1(X0_50) != iProver_top
% 5.94/1.46      | v1_funct_1(X3_50) != iProver_top
% 5.94/1.46      | v1_xboole_0(X5_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X2_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X4_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X1_50) = iProver_top ),
% 5.94/1.46      inference(predicate_to_equality,[status(thm)],[c_563]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_2253,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(X0_50,X1_50,X2_50),X3_50,k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50) = k7_relat_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50)
% 5.94/1.46      | v1_funct_2(X5_50,X2_50,X3_50) != iProver_top
% 5.94/1.46      | v1_funct_2(X4_50,X1_50,X3_50) != iProver_top
% 5.94/1.46      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 5.94/1.46      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X3_50))) != iProver_top
% 5.94/1.46      | v1_funct_1(X5_50) != iProver_top
% 5.94/1.46      | v1_funct_1(X4_50) != iProver_top
% 5.94/1.46      | v1_funct_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50)) != iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X3_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X1_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X2_50) = iProver_top ),
% 5.94/1.46      inference(superposition,[status(thm)],[c_961,c_959]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_561,plain,
% 5.94/1.46      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 5.94/1.46      | ~ v1_funct_2(X3_50,X4_50,X2_50)
% 5.94/1.46      | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
% 5.94/1.46      | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
% 5.94/1.46      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 5.94/1.46      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
% 5.94/1.46      | ~ v1_funct_1(X0_50)
% 5.94/1.46      | ~ v1_funct_1(X3_50)
% 5.94/1.46      | v1_funct_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50))
% 5.94/1.46      | v1_xboole_0(X1_50)
% 5.94/1.46      | v1_xboole_0(X2_50)
% 5.94/1.46      | v1_xboole_0(X4_50)
% 5.94/1.46      | v1_xboole_0(X5_50) ),
% 5.94/1.46      inference(subtyping,[status(esa)],[c_13]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_963,plain,
% 5.94/1.46      ( v1_funct_2(X0_50,X1_50,X2_50) != iProver_top
% 5.94/1.46      | v1_funct_2(X3_50,X4_50,X2_50) != iProver_top
% 5.94/1.46      | m1_subset_1(X4_50,k1_zfmisc_1(X5_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X1_50,k1_zfmisc_1(X5_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50))) != iProver_top
% 5.94/1.46      | m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50))) != iProver_top
% 5.94/1.46      | v1_funct_1(X0_50) != iProver_top
% 5.94/1.46      | v1_funct_1(X3_50) != iProver_top
% 5.94/1.46      | v1_funct_1(k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50)) = iProver_top
% 5.94/1.46      | v1_xboole_0(X5_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X2_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X4_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X1_50) = iProver_top ),
% 5.94/1.46      inference(predicate_to_equality,[status(thm)],[c_561]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_6514,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(X0_50,X1_50,X2_50),X3_50,k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50) = k7_relat_1(k1_tmap_1(X0_50,X3_50,X1_50,X2_50,X4_50,X5_50),X6_50)
% 5.94/1.46      | v1_funct_2(X5_50,X2_50,X3_50) != iProver_top
% 5.94/1.46      | v1_funct_2(X4_50,X1_50,X3_50) != iProver_top
% 5.94/1.46      | m1_subset_1(X2_50,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X2_50,X3_50))) != iProver_top
% 5.94/1.46      | m1_subset_1(X4_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X3_50))) != iProver_top
% 5.94/1.46      | v1_funct_1(X5_50) != iProver_top
% 5.94/1.46      | v1_funct_1(X4_50) != iProver_top
% 5.94/1.46      | v1_xboole_0(X2_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X1_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X3_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top ),
% 5.94/1.46      inference(forward_subsumption_resolution,
% 5.94/1.46                [status(thm)],
% 5.94/1.46                [c_2253,c_963]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_6518,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
% 5.94/1.46      | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
% 5.94/1.46      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 5.94/1.46      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | v1_funct_1(X2_50) != iProver_top
% 5.94/1.46      | v1_funct_1(sK5) != iProver_top
% 5.94/1.46      | v1_xboole_0(X1_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(sK1) = iProver_top
% 5.94/1.46      | v1_xboole_0(sK3) = iProver_top ),
% 5.94/1.46      inference(superposition,[status(thm)],[c_964,c_6514]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_6787,plain,
% 5.94/1.46      ( v1_funct_1(X2_50) != iProver_top
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
% 5.94/1.46      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
% 5.94/1.46      | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
% 5.94/1.46      | v1_xboole_0(X1_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top ),
% 5.94/1.46      inference(global_propositional_subsumption,
% 5.94/1.46                [status(thm)],
% 5.94/1.46                [c_6518,c_29,c_32,c_38,c_39]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_6788,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(X0_50,X1_50,sK3),sK1,k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,X1_50,sK3,X2_50,sK5),X3_50)
% 5.94/1.46      | v1_funct_2(X2_50,X1_50,sK1) != iProver_top
% 5.94/1.46      | m1_subset_1(X1_50,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,sK1))) != iProver_top
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | v1_funct_1(X2_50) != iProver_top
% 5.94/1.46      | v1_xboole_0(X1_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top ),
% 5.94/1.46      inference(renaming,[status(thm)],[c_6787]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_6802,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
% 5.94/1.46      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | v1_funct_1(sK4) != iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(sK2) = iProver_top ),
% 5.94/1.46      inference(superposition,[status(thm)],[c_967,c_6788]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_7247,plain,
% 5.94/1.46      ( v1_xboole_0(X0_50) = iProver_top
% 5.94/1.46      | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
% 5.94/1.46      inference(global_propositional_subsumption,
% 5.94/1.46                [status(thm)],
% 5.94/1.46                [c_6802,c_30,c_35,c_36]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_7248,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50) = k7_relat_1(k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),X1_50)
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top ),
% 5.94/1.46      inference(renaming,[status(thm)],[c_7247]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_7257,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50)
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.46      inference(superposition,[status(thm)],[c_970,c_7248]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_27,negated_conjecture,
% 5.94/1.46      ( ~ v1_xboole_0(sK0) ),
% 5.94/1.46      inference(cnf_transformation,[],[f49]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_28,plain,
% 5.94/1.46      ( v1_xboole_0(sK0) != iProver_top ),
% 5.94/1.46      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_24,negated_conjecture,
% 5.94/1.46      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 5.94/1.46      inference(cnf_transformation,[],[f52]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_31,plain,
% 5.94/1.46      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 5.94/1.46      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_7492,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_50) ),
% 5.94/1.46      inference(global_propositional_subsumption,
% 5.94/1.46                [status(thm)],
% 5.94/1.46                [c_7257,c_28,c_31]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_13792,plain,
% 5.94/1.46      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 5.94/1.46      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.46      inference(demodulation,[status(thm)],[c_13791,c_2022,c_7492]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_1670,plain,
% 5.94/1.46      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 5.94/1.46      inference(superposition,[status(thm)],[c_967,c_978]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_13793,plain,
% 5.94/1.46      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 5.94/1.46      | k1_xboole_0 != k1_xboole_0
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.46      inference(light_normalisation,[status(thm)],[c_13792,c_544,c_1670]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_13794,plain,
% 5.94/1.46      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.46      inference(equality_resolution_simp,[status(thm)],[c_13793]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_10,plain,
% 5.94/1.46      ( ~ v1_funct_2(X0,X1,X2)
% 5.94/1.46      | ~ v1_funct_2(X3,X4,X2)
% 5.94/1.46      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 5.94/1.46      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.94/1.46      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.94/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.46      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.94/1.46      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 5.94/1.46      | ~ v1_funct_1(X0)
% 5.94/1.46      | ~ v1_funct_1(X3)
% 5.94/1.46      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 5.94/1.46      | v1_xboole_0(X5)
% 5.94/1.46      | v1_xboole_0(X2)
% 5.94/1.46      | v1_xboole_0(X4)
% 5.94/1.46      | v1_xboole_0(X1)
% 5.94/1.46      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.94/1.46      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 5.94/1.46      inference(cnf_transformation,[],[f66]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_152,plain,
% 5.94/1.46      ( ~ v1_funct_1(X3)
% 5.94/1.46      | ~ v1_funct_1(X0)
% 5.94/1.46      | ~ v1_funct_2(X3,X4,X2)
% 5.94/1.46      | ~ v1_funct_2(X0,X1,X2)
% 5.94/1.46      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.94/1.46      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.94/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.46      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.94/1.46      | v1_xboole_0(X5)
% 5.94/1.46      | v1_xboole_0(X2)
% 5.94/1.46      | v1_xboole_0(X4)
% 5.94/1.46      | v1_xboole_0(X1)
% 5.94/1.46      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.94/1.46      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 5.94/1.46      inference(global_propositional_subsumption,
% 5.94/1.46                [status(thm)],
% 5.94/1.46                [c_10,c_13,c_12,c_11]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_153,plain,
% 5.94/1.46      ( ~ v1_funct_2(X0,X1,X2)
% 5.94/1.46      | ~ v1_funct_2(X3,X4,X2)
% 5.94/1.46      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 5.94/1.46      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 5.94/1.46      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 5.94/1.46      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 5.94/1.46      | ~ v1_funct_1(X0)
% 5.94/1.46      | ~ v1_funct_1(X3)
% 5.94/1.46      | v1_xboole_0(X1)
% 5.94/1.46      | v1_xboole_0(X2)
% 5.94/1.46      | v1_xboole_0(X4)
% 5.94/1.46      | v1_xboole_0(X5)
% 5.94/1.46      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 5.94/1.46      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 5.94/1.46      inference(renaming,[status(thm)],[c_152]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_547,plain,
% 5.94/1.46      ( ~ v1_funct_2(X0_50,X1_50,X2_50)
% 5.94/1.46      | ~ v1_funct_2(X3_50,X4_50,X2_50)
% 5.94/1.46      | ~ m1_subset_1(X4_50,k1_zfmisc_1(X5_50))
% 5.94/1.46      | ~ m1_subset_1(X1_50,k1_zfmisc_1(X5_50))
% 5.94/1.46      | ~ m1_subset_1(X0_50,k1_zfmisc_1(k2_zfmisc_1(X1_50,X2_50)))
% 5.94/1.46      | ~ m1_subset_1(X3_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X2_50)))
% 5.94/1.46      | ~ v1_funct_1(X0_50)
% 5.94/1.46      | ~ v1_funct_1(X3_50)
% 5.94/1.46      | v1_xboole_0(X1_50)
% 5.94/1.46      | v1_xboole_0(X2_50)
% 5.94/1.46      | v1_xboole_0(X4_50)
% 5.94/1.46      | v1_xboole_0(X5_50)
% 5.94/1.46      | k2_partfun1(X1_50,X2_50,X0_50,k9_subset_1(X5_50,X4_50,X1_50)) != k2_partfun1(X4_50,X2_50,X3_50,k9_subset_1(X5_50,X4_50,X1_50))
% 5.94/1.46      | k2_partfun1(k4_subset_1(X5_50,X4_50,X1_50),X2_50,k1_tmap_1(X5_50,X2_50,X4_50,X1_50,X3_50,X0_50),X4_50) = X3_50 ),
% 5.94/1.46      inference(subtyping,[status(esa)],[c_153]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_976,plain,
% 5.94/1.46      ( k2_partfun1(X0_50,X1_50,X2_50,k9_subset_1(X3_50,X4_50,X0_50)) != k2_partfun1(X4_50,X1_50,X5_50,k9_subset_1(X3_50,X4_50,X0_50))
% 5.94/1.46      | k2_partfun1(k4_subset_1(X3_50,X4_50,X0_50),X1_50,k1_tmap_1(X3_50,X1_50,X4_50,X0_50,X5_50,X2_50),X4_50) = X5_50
% 5.94/1.46      | v1_funct_2(X2_50,X0_50,X1_50) != iProver_top
% 5.94/1.46      | v1_funct_2(X5_50,X4_50,X1_50) != iProver_top
% 5.94/1.46      | m1_subset_1(X4_50,k1_zfmisc_1(X3_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X0_50,k1_zfmisc_1(X3_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X2_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,X1_50))) != iProver_top
% 5.94/1.46      | m1_subset_1(X5_50,k1_zfmisc_1(k2_zfmisc_1(X4_50,X1_50))) != iProver_top
% 5.94/1.46      | v1_funct_1(X2_50) != iProver_top
% 5.94/1.46      | v1_funct_1(X5_50) != iProver_top
% 5.94/1.46      | v1_xboole_0(X3_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X1_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X4_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top ),
% 5.94/1.46      inference(predicate_to_equality,[status(thm)],[c_547]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_3158,plain,
% 5.94/1.46      ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 5.94/1.46      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
% 5.94/1.46      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 5.94/1.46      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 5.94/1.46      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 5.94/1.46      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.46      | v1_funct_1(X1_50) != iProver_top
% 5.94/1.46      | v1_funct_1(sK5) != iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X2_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(sK1) = iProver_top
% 5.94/1.46      | v1_xboole_0(sK3) = iProver_top ),
% 5.94/1.46      inference(superposition,[status(thm)],[c_2669,c_976]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_4596,plain,
% 5.94/1.46      ( v1_funct_1(X1_50) != iProver_top
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.46      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 5.94/1.46      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
% 5.94/1.46      | k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 5.94/1.46      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X2_50) = iProver_top ),
% 5.94/1.46      inference(global_propositional_subsumption,
% 5.94/1.46                [status(thm)],
% 5.94/1.46                [c_3158,c_29,c_32,c_38,c_39,c_40]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_4597,plain,
% 5.94/1.46      ( k2_partfun1(X0_50,sK1,X1_50,k9_subset_1(X2_50,X0_50,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_50,X0_50,sK3))
% 5.94/1.46      | k2_partfun1(k4_subset_1(X2_50,X0_50,sK3),sK1,k1_tmap_1(X2_50,sK1,X0_50,sK3,X1_50,sK5),X0_50) = X1_50
% 5.94/1.46      | v1_funct_2(X1_50,X0_50,sK1) != iProver_top
% 5.94/1.46      | m1_subset_1(X0_50,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(X1_50,k1_zfmisc_1(k2_zfmisc_1(X0_50,sK1))) != iProver_top
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X2_50)) != iProver_top
% 5.94/1.46      | v1_funct_1(X1_50) != iProver_top
% 5.94/1.46      | v1_xboole_0(X2_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top ),
% 5.94/1.46      inference(renaming,[status(thm)],[c_4596]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_4612,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 5.94/1.46      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 5.94/1.46      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 5.94/1.46      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | v1_funct_1(sK4) != iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top
% 5.94/1.46      | v1_xboole_0(sK2) = iProver_top ),
% 5.94/1.46      inference(superposition,[status(thm)],[c_2749,c_4597]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_10555,plain,
% 5.94/1.46      ( v1_xboole_0(X0_50) = iProver_top
% 5.94/1.46      | k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 5.94/1.46      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top ),
% 5.94/1.46      inference(global_propositional_subsumption,
% 5.94/1.46                [status(thm)],
% 5.94/1.46                [c_4612,c_30,c_35,c_36,c_37]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_10556,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(X0_50,sK2,sK3),sK1,k1_tmap_1(X0_50,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 5.94/1.46      | k7_relat_1(sK5,k9_subset_1(X0_50,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_50,sK2,sK3))
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(X0_50)) != iProver_top
% 5.94/1.46      | v1_xboole_0(X0_50) = iProver_top ),
% 5.94/1.46      inference(renaming,[status(thm)],[c_10555]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_10566,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 5.94/1.46      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.46      inference(superposition,[status(thm)],[c_2022,c_10556]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_10567,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 5.94/1.46      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.46      inference(light_normalisation,[status(thm)],[c_10566,c_544,c_1669]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_10568,plain,
% 5.94/1.46      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 5.94/1.46      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.46      inference(demodulation,[status(thm)],[c_10567,c_2022,c_7492]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_10569,plain,
% 5.94/1.46      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 5.94/1.46      | k1_xboole_0 != k1_xboole_0
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.46      inference(light_normalisation,[status(thm)],[c_10568,c_544,c_1670]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_10570,plain,
% 5.94/1.46      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 5.94/1.46      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 5.94/1.46      | v1_xboole_0(sK0) = iProver_top ),
% 5.94/1.46      inference(equality_resolution_simp,[status(thm)],[c_10569]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_14,negated_conjecture,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 5.94/1.46      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 5.94/1.46      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 5.94/1.46      inference(cnf_transformation,[],[f62]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_560,negated_conjecture,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 5.94/1.46      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 5.94/1.46      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 5.94/1.46      inference(subtyping,[status(esa)],[c_14]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_2087,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 5.94/1.46      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 5.94/1.46      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 5.94/1.46      inference(demodulation,[status(thm)],[c_2022,c_560]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_2088,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 5.94/1.46      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 5.94/1.46      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 5.94/1.46      inference(light_normalisation,[status(thm)],[c_2087,c_544]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_2753,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 5.94/1.46      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 5.94/1.46      | k1_xboole_0 != k1_xboole_0 ),
% 5.94/1.46      inference(demodulation,
% 5.94/1.46                [status(thm)],
% 5.94/1.46                [c_2088,c_1669,c_1670,c_2669,c_2749]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_2754,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 5.94/1.46      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 5.94/1.46      inference(equality_resolution_simp,[status(thm)],[c_2753]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_7496,plain,
% 5.94/1.46      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 5.94/1.46      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 5.94/1.46      inference(demodulation,[status(thm)],[c_7492,c_2754]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_7497,plain,
% 5.94/1.46      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 5.94/1.46      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 5.94/1.46      inference(demodulation,[status(thm)],[c_7496,c_7492]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(c_33,plain,
% 5.94/1.46      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 5.94/1.46      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 5.94/1.46  
% 5.94/1.46  cnf(contradiction,plain,
% 5.94/1.46      ( $false ),
% 5.94/1.46      inference(minisat,
% 5.94/1.46                [status(thm)],
% 5.94/1.46                [c_13794,c_10570,c_7497,c_33,c_31,c_28]) ).
% 5.94/1.46  
% 5.94/1.46  
% 5.94/1.46  % SZS output end CNFRefutation for theBenchmark.p
% 5.94/1.46  
% 5.94/1.46  ------                               Statistics
% 5.94/1.46  
% 5.94/1.46  ------ General
% 5.94/1.46  
% 5.94/1.46  abstr_ref_over_cycles:                  0
% 5.94/1.46  abstr_ref_under_cycles:                 0
% 5.94/1.46  gc_basic_clause_elim:                   0
% 5.94/1.46  forced_gc_time:                         0
% 5.94/1.46  parsing_time:                           0.012
% 5.94/1.46  unif_index_cands_time:                  0.
% 5.94/1.46  unif_index_add_time:                    0.
% 5.94/1.46  orderings_time:                         0.
% 5.94/1.46  out_proof_time:                         0.014
% 5.94/1.46  total_time:                             0.737
% 5.94/1.46  num_of_symbols:                         55
% 5.94/1.46  num_of_terms:                           30349
% 5.94/1.46  
% 5.94/1.46  ------ Preprocessing
% 5.94/1.46  
% 5.94/1.46  num_of_splits:                          0
% 5.94/1.46  num_of_split_atoms:                     0
% 5.94/1.46  num_of_reused_defs:                     0
% 5.94/1.46  num_eq_ax_congr_red:                    8
% 5.94/1.46  num_of_sem_filtered_clauses:            1
% 5.94/1.46  num_of_subtypes:                        2
% 5.94/1.46  monotx_restored_types:                  0
% 5.94/1.46  sat_num_of_epr_types:                   0
% 5.94/1.46  sat_num_of_non_cyclic_types:            0
% 5.94/1.46  sat_guarded_non_collapsed_types:        1
% 5.94/1.46  num_pure_diseq_elim:                    0
% 5.94/1.46  simp_replaced_by:                       0
% 5.94/1.46  res_preprocessed:                       128
% 5.94/1.46  prep_upred:                             0
% 5.94/1.46  prep_unflattend:                        4
% 5.94/1.46  smt_new_axioms:                         0
% 5.94/1.46  pred_elim_cands:                        4
% 5.94/1.46  pred_elim:                              3
% 5.94/1.46  pred_elim_cl:                           5
% 5.94/1.46  pred_elim_cycles:                       5
% 5.94/1.46  merged_defs:                            2
% 5.94/1.46  merged_defs_ncl:                        0
% 5.94/1.46  bin_hyper_res:                          2
% 5.94/1.46  prep_cycles:                            4
% 5.94/1.46  pred_elim_time:                         0.002
% 5.94/1.46  splitting_time:                         0.
% 5.94/1.46  sem_filter_time:                        0.
% 5.94/1.46  monotx_time:                            0.
% 5.94/1.46  subtype_inf_time:                       0.
% 5.94/1.46  
% 5.94/1.46  ------ Problem properties
% 5.94/1.46  
% 5.94/1.46  clauses:                                23
% 5.94/1.46  conjectures:                            13
% 5.94/1.46  epr:                                    8
% 5.94/1.46  horn:                                   17
% 5.94/1.46  ground:                                 14
% 5.94/1.46  unary:                                  13
% 5.94/1.46  binary:                                 2
% 5.94/1.46  lits:                                   107
% 5.94/1.46  lits_eq:                                13
% 5.94/1.46  fd_pure:                                0
% 5.94/1.46  fd_pseudo:                              0
% 5.94/1.46  fd_cond:                                0
% 5.94/1.46  fd_pseudo_cond:                         0
% 5.94/1.46  ac_symbols:                             0
% 5.94/1.46  
% 5.94/1.46  ------ Propositional Solver
% 5.94/1.46  
% 5.94/1.46  prop_solver_calls:                      27
% 5.94/1.46  prop_fast_solver_calls:                 2785
% 5.94/1.46  smt_solver_calls:                       0
% 5.94/1.46  smt_fast_solver_calls:                  0
% 5.94/1.46  prop_num_of_clauses:                    5494
% 5.94/1.46  prop_preprocess_simplified:             8867
% 5.94/1.46  prop_fo_subsumed:                       205
% 5.94/1.46  prop_solver_time:                       0.
% 5.94/1.46  smt_solver_time:                        0.
% 5.94/1.46  smt_fast_solver_time:                   0.
% 5.94/1.46  prop_fast_solver_time:                  0.
% 5.94/1.46  prop_unsat_core_time:                   0.
% 5.94/1.46  
% 5.94/1.46  ------ QBF
% 5.94/1.46  
% 5.94/1.46  qbf_q_res:                              0
% 5.94/1.46  qbf_num_tautologies:                    0
% 5.94/1.46  qbf_prep_cycles:                        0
% 5.94/1.46  
% 5.94/1.46  ------ BMC1
% 5.94/1.46  
% 5.94/1.46  bmc1_current_bound:                     -1
% 5.94/1.46  bmc1_last_solved_bound:                 -1
% 5.94/1.46  bmc1_unsat_core_size:                   -1
% 5.94/1.46  bmc1_unsat_core_parents_size:           -1
% 5.94/1.46  bmc1_merge_next_fun:                    0
% 5.94/1.46  bmc1_unsat_core_clauses_time:           0.
% 5.94/1.46  
% 5.94/1.46  ------ Instantiation
% 5.94/1.46  
% 5.94/1.46  inst_num_of_clauses:                    1224
% 5.94/1.46  inst_num_in_passive:                    186
% 5.94/1.46  inst_num_in_active:                     588
% 5.94/1.46  inst_num_in_unprocessed:                450
% 5.94/1.46  inst_num_of_loops:                      600
% 5.94/1.46  inst_num_of_learning_restarts:          0
% 5.94/1.46  inst_num_moves_active_passive:          8
% 5.94/1.46  inst_lit_activity:                      0
% 5.94/1.46  inst_lit_activity_moves:                0
% 5.94/1.46  inst_num_tautologies:                   0
% 5.94/1.46  inst_num_prop_implied:                  0
% 5.94/1.46  inst_num_existing_simplified:           0
% 5.94/1.46  inst_num_eq_res_simplified:             0
% 5.94/1.46  inst_num_child_elim:                    0
% 5.94/1.46  inst_num_of_dismatching_blockings:      163
% 5.94/1.46  inst_num_of_non_proper_insts:           829
% 5.94/1.46  inst_num_of_duplicates:                 0
% 5.94/1.46  inst_inst_num_from_inst_to_res:         0
% 5.94/1.46  inst_dismatching_checking_time:         0.
% 5.94/1.46  
% 5.94/1.46  ------ Resolution
% 5.94/1.46  
% 5.94/1.46  res_num_of_clauses:                     0
% 5.94/1.46  res_num_in_passive:                     0
% 5.94/1.46  res_num_in_active:                      0
% 5.94/1.46  res_num_of_loops:                       132
% 5.94/1.46  res_forward_subset_subsumed:            35
% 5.94/1.46  res_backward_subset_subsumed:           0
% 5.94/1.46  res_forward_subsumed:                   0
% 5.94/1.46  res_backward_subsumed:                  0
% 5.94/1.46  res_forward_subsumption_resolution:     0
% 5.94/1.46  res_backward_subsumption_resolution:    0
% 5.94/1.46  res_clause_to_clause_subsumption:       2048
% 5.94/1.46  res_orphan_elimination:                 0
% 5.94/1.46  res_tautology_del:                      27
% 5.94/1.46  res_num_eq_res_simplified:              0
% 5.94/1.46  res_num_sel_changes:                    0
% 5.94/1.46  res_moves_from_active_to_pass:          0
% 5.94/1.46  
% 5.94/1.46  ------ Superposition
% 5.94/1.46  
% 5.94/1.46  sup_time_total:                         0.
% 5.94/1.46  sup_time_generating:                    0.
% 5.94/1.46  sup_time_sim_full:                      0.
% 5.94/1.46  sup_time_sim_immed:                     0.
% 5.94/1.46  
% 5.94/1.46  sup_num_of_clauses:                     214
% 5.94/1.46  sup_num_in_active:                      116
% 5.94/1.46  sup_num_in_passive:                     98
% 5.94/1.46  sup_num_of_loops:                       118
% 5.94/1.46  sup_fw_superposition:                   180
% 5.94/1.46  sup_bw_superposition:                   55
% 5.94/1.46  sup_immediate_simplified:               114
% 5.94/1.46  sup_given_eliminated:                   0
% 5.94/1.46  comparisons_done:                       0
% 5.94/1.46  comparisons_avoided:                    0
% 5.94/1.46  
% 5.94/1.46  ------ Simplifications
% 5.94/1.46  
% 5.94/1.46  
% 5.94/1.46  sim_fw_subset_subsumed:                 2
% 5.94/1.46  sim_bw_subset_subsumed:                 1
% 5.94/1.46  sim_fw_subsumed:                        11
% 5.94/1.46  sim_bw_subsumed:                        8
% 5.94/1.46  sim_fw_subsumption_res:                 1
% 5.94/1.46  sim_bw_subsumption_res:                 0
% 5.94/1.46  sim_tautology_del:                      0
% 5.94/1.46  sim_eq_tautology_del:                   9
% 5.94/1.46  sim_eq_res_simp:                        6
% 5.94/1.46  sim_fw_demodulated:                     60
% 5.94/1.46  sim_bw_demodulated:                     3
% 5.94/1.46  sim_light_normalised:                   50
% 5.94/1.46  sim_joinable_taut:                      0
% 5.94/1.46  sim_joinable_simp:                      0
% 5.94/1.46  sim_ac_normalised:                      0
% 5.94/1.46  sim_smt_subsumption:                    0
% 5.94/1.46  
%------------------------------------------------------------------------------
