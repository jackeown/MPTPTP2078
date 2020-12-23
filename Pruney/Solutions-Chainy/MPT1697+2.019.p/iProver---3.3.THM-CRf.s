%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:25 EST 2020

% Result     : Theorem 31.83s
% Output     : CNFRefutation 31.83s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_56479)

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

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,(
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

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f54,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f42,f53,f52,f51,f50,f49,f48])).

fof(f87,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

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

fof(f37,plain,(
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

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f95,plain,(
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
    inference(equality_resolution,[],[f73])).

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

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f75,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f40])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f40])).

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

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f79,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f82,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f89,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
       => r1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_subset_1(X1,X0)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f72,plain,(
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
    inference(cnf_transformation,[],[f47])).

fof(f96,plain,(
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
    inference(equality_resolution,[],[f72])).

fof(f91,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_660,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1553,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_669,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1545,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X2_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_4660,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_1545])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2098,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_2379,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(instantiation,[status(thm)],[c_2098])).

cnf(c_5080,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4660,c_29,c_27,c_2379])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_656,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1557,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_682,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1532,plain,
    ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_2248,plain,
    ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
    inference(superposition,[status(thm)],[c_1557,c_1532])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_663,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1550,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_663])).

cnf(c_4659,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_1545])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2093,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_2374,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(instantiation,[status(thm)],[c_2093])).

cnf(c_5074,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4659,c_26,c_24,c_2374])).

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
    inference(cnf_transformation,[],[f95])).

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
    inference(cnf_transformation,[],[f75])).

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
    inference(cnf_transformation,[],[f76])).

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
    inference(cnf_transformation,[],[f77])).

cnf(c_380,plain,
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

cnf(c_381,plain,
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
    inference(renaming,[status(thm)],[c_380])).

cnf(c_649,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53)
    | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
    | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_1564,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_649])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_681,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1533,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
    | v1_xboole_0(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_1813,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1564,c_1533])).

cnf(c_10245,plain,
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
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5074,c_1813])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_38,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_41,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_47,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_48,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_52419,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10245,c_38,c_41,c_47,c_48,c_49])).

cnf(c_52420,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_52419])).

cnf(c_52439,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_52420])).

cnf(c_52448,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_52439,c_2248])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_70225,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52448,c_38,c_47,c_48,c_49,c_56479])).

cnf(c_70226,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_70225])).

cnf(c_70239,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5080,c_70226])).

cnf(c_30,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_657,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1556,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_8,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_676,plain,
    ( ~ r1_subset_1(X0_53,X1_53)
    | r1_xboole_0(X0_53,X1_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1538,plain,
    ( r1_subset_1(X0_53,X1_53) != iProver_top
    | r1_xboole_0(X0_53,X1_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_3853,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_1538])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_39,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_43,plain,
    ( r1_subset_1(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2009,plain,
    ( ~ r1_subset_1(sK2,sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_2010,plain,
    ( r1_subset_1(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2009])).

cnf(c_3856,plain,
    ( r1_xboole_0(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3853,c_39,c_41,c_43,c_2010])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_683,plain,
    ( ~ r1_xboole_0(X0_53,X1_53)
    | k3_xboole_0(X0_53,X1_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1531,plain,
    ( k3_xboole_0(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X0_53,X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_3862,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3856,c_1531])).

cnf(c_9,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_subset_1(X1,X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_675,plain,
    ( ~ r1_subset_1(X0_53,X1_53)
    | r1_subset_1(X1_53,X0_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1539,plain,
    ( r1_subset_1(X0_53,X1_53) != iProver_top
    | r1_subset_1(X1_53,X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_4527,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_1539])).

cnf(c_2006,plain,
    ( r1_subset_1(sK3,sK2)
    | ~ r1_subset_1(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_2007,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top
    | r1_subset_1(sK2,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2006])).

cnf(c_4828,plain,
    ( r1_subset_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4527,c_39,c_41,c_43,c_2007])).

cnf(c_4834,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4828,c_1538])).

cnf(c_2236,plain,
    ( ~ r1_subset_1(sK3,sK2)
    | r1_xboole_0(sK3,sK2)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_2238,plain,
    ( r1_subset_1(sK3,sK2) != iProver_top
    | r1_xboole_0(sK3,sK2) = iProver_top
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2236])).

cnf(c_5696,plain,
    ( r1_xboole_0(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4834,c_39,c_41,c_43,c_2007,c_2238])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_672,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | v1_partfun1(X0_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | v1_xboole_0(X2_53) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1542,plain,
    ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
    | v1_partfun1(X0_53,X1_53) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_4808,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_1542])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2108,plain,
    ( ~ v1_funct_2(sK4,X0_53,X1_53)
    | v1_partfun1(sK4,X0_53)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_53) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_2387,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | v1_partfun1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_2388,plain,
    ( v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_partfun1(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2387])).

cnf(c_5206,plain,
    ( v1_partfun1(sK4,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4808,c_38,c_44,c_45,c_46,c_2388])).

cnf(c_15,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_670,plain,
    ( ~ v1_partfun1(X0_53,X1_53)
    | ~ v4_relat_1(X0_53,X1_53)
    | ~ v1_relat_1(X0_53)
    | k1_relat_1(X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1544,plain,
    ( k1_relat_1(X0_53) = X1_53
    | v1_partfun1(X0_53,X1_53) != iProver_top
    | v4_relat_1(X0_53,X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_670])).

cnf(c_5211,plain,
    ( k1_relat_1(sK4) = sK2
    | v4_relat_1(sK4,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5206,c_1544])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1971,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_673,plain,
    ( v4_relat_1(X0_53,X1_53)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2003,plain,
    ( v4_relat_1(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_2213,plain,
    ( ~ v1_partfun1(sK4,X0_53)
    | ~ v4_relat_1(sK4,X0_53)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = X0_53 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_2220,plain,
    ( ~ v1_partfun1(sK4,sK2)
    | ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_2213])).

cnf(c_5383,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5211,c_35,c_29,c_28,c_27,c_1971,c_2003,c_2220,c_2387])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_679,plain,
    ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1535,plain,
    ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
    | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_5387,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,sK2) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5383,c_1535])).

cnf(c_1972,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1971])).

cnf(c_6217,plain,
    ( r1_xboole_0(X0_53,sK2) != iProver_top
    | k7_relat_1(sK4,X0_53) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5387,c_46,c_1972])).

cnf(c_6218,plain,
    ( k7_relat_1(sK4,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6217])).

cnf(c_6225,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5696,c_6218])).

cnf(c_1541,plain,
    ( v4_relat_1(X0_53,X1_53) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_2839,plain,
    ( v4_relat_1(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_1541])).

cnf(c_6,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_678,plain,
    ( ~ v4_relat_1(X0_53,X1_53)
    | ~ v1_relat_1(X0_53)
    | k7_relat_1(X0_53,X1_53) = X0_53 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1536,plain,
    ( k7_relat_1(X0_53,X1_53) = X0_53
    | v4_relat_1(X0_53,X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_3619,plain,
    ( k7_relat_1(sK4,sK2) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2839,c_1536])).

cnf(c_2214,plain,
    ( ~ v4_relat_1(sK4,X0_53)
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,X0_53) = sK4 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_2216,plain,
    ( ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,sK2) = sK4 ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_4199,plain,
    ( k7_relat_1(sK4,sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3619,c_27,c_1971,c_2003,c_2216])).

cnf(c_1540,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
    | v1_relat_1(X0_53) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_2751,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_1540])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_680,plain,
    ( ~ v1_relat_1(X0_53)
    | k7_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1534,plain,
    ( k7_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53))
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_2930,plain,
    ( k7_relat_1(sK4,k3_xboole_0(X0_53,X1_53)) = k7_relat_1(k7_relat_1(sK4,X0_53),X1_53) ),
    inference(superposition,[status(thm)],[c_2751,c_1534])).

cnf(c_4202,plain,
    ( k7_relat_1(sK4,k3_xboole_0(sK2,X0_53)) = k7_relat_1(sK4,X0_53) ),
    inference(superposition,[status(thm)],[c_4199,c_2930])).

cnf(c_4325,plain,
    ( k7_relat_1(sK4,sK3) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3862,c_4202])).

cnf(c_6606,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6225,c_4325])).

cnf(c_70327,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_70239,c_3862,c_6606])).

cnf(c_667,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1547,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_1758,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1547,c_1533])).

cnf(c_7266,plain,
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
    inference(superposition,[status(thm)],[c_1758,c_1545])).

cnf(c_665,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1549,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_1706,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1549,c_1533])).

cnf(c_13023,plain,
    ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
    | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
    | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
    | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
    | v1_funct_1(X5_53) != iProver_top
    | v1_funct_1(X4_53) != iProver_top
    | v1_xboole_0(X2_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X3_53) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7266,c_1706])).

cnf(c_13028,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,X1_53),sK1,k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1553,c_13023])).

cnf(c_13899,plain,
    ( v1_funct_1(X2_53) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_53,sK2,X1_53),sK1,k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13028,c_38,c_39,c_44,c_45])).

cnf(c_13900,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,X1_53),sK1,k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53)
    | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_13899])).

cnf(c_13912,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_13900])).

cnf(c_14429,plain,
    ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13912,c_41,c_47,c_48])).

cnf(c_14438,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_14429])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14443,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14438,c_40])).

cnf(c_70328,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_70327,c_14443])).

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
    inference(cnf_transformation,[],[f96])).

cnf(c_371,plain,
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

cnf(c_372,plain,
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
    inference(renaming,[status(thm)],[c_371])).

cnf(c_650,plain,
    ( ~ v1_funct_2(X0_53,X1_53,X2_53)
    | ~ v1_funct_2(X3_53,X4_53,X2_53)
    | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
    | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X3_53)
    | v1_xboole_0(X1_53)
    | v1_xboole_0(X2_53)
    | v1_xboole_0(X4_53)
    | v1_xboole_0(X5_53)
    | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
    | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
    inference(subtyping,[status(esa)],[c_372])).

cnf(c_1563,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_1785,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1563,c_1533])).

cnf(c_8467,plain,
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
    inference(superposition,[status(thm)],[c_5074,c_1785])).

cnf(c_28843,plain,
    ( v1_funct_1(X1_53) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8467,c_38,c_41,c_47,c_48,c_49])).

cnf(c_28844,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
    | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_28843])).

cnf(c_28863,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_28844])).

cnf(c_28872,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28863,c_2248])).

cnf(c_8471,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(sK0,X0_53,sK3)) != k2_partfun1(sK3,X1_53,X3_53,k3_xboole_0(X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),X1_53,k1_tmap_1(sK0,X1_53,X0_53,sK3,X2_53,X3_53),X0_53) = X2_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X3_53,sK3,X1_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_53))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2248,c_1785])).

cnf(c_8528,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k3_xboole_0(X0_53,sK3)) != k2_partfun1(sK3,X1_53,X3_53,k3_xboole_0(X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),X1_53,k1_tmap_1(sK0,X1_53,X0_53,sK3,X2_53,X3_53),X0_53) = X2_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X3_53,sK3,X1_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_53))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8471,c_2248])).

cnf(c_33948,plain,
    ( v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | k2_partfun1(X0_53,X1_53,X2_53,k3_xboole_0(X0_53,sK3)) != k2_partfun1(sK3,X1_53,X3_53,k3_xboole_0(X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),X1_53,k1_tmap_1(sK0,X1_53,X0_53,sK3,X2_53,X3_53),X0_53) = X2_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X3_53,sK3,X1_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_53))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8528,c_41,c_42])).

cnf(c_33949,plain,
    ( k2_partfun1(X0_53,X1_53,X2_53,k3_xboole_0(X0_53,sK3)) != k2_partfun1(sK3,X1_53,X3_53,k3_xboole_0(X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),X1_53,k1_tmap_1(sK0,X1_53,X0_53,sK3,X2_53,X3_53),X0_53) = X2_53
    | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
    | v1_funct_2(X3_53,sK3,X1_53) != iProver_top
    | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_53))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X3_53) != iProver_top
    | v1_funct_1(X2_53) != iProver_top
    | v1_xboole_0(X1_53) = iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_33948])).

cnf(c_33971,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5074,c_33949])).

cnf(c_59367,plain,
    ( m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28872,c_42])).

cnf(c_59368,plain,
    ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
    | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
    | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_xboole_0(X0_53) = iProver_top ),
    inference(renaming,[status(thm)],[c_59367])).

cnf(c_59381,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5080,c_59368])).

cnf(c_59469,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_59381,c_3862,c_6606])).

cnf(c_59470,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_59469,c_14443])).

cnf(c_4807,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_1542])).

cnf(c_2103,plain,
    ( ~ v1_funct_2(sK5,X0_53,X1_53)
    | v1_partfun1(sK5,X0_53)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_53) ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_2384,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | v1_partfun1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2103])).

cnf(c_2385,plain,
    ( v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_partfun1(sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2384])).

cnf(c_5198,plain,
    ( v1_partfun1(sK5,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4807,c_38,c_47,c_48,c_49,c_2385])).

cnf(c_5203,plain,
    ( k1_relat_1(sK5) = sK3
    | v4_relat_1(sK5,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5198,c_1544])).

cnf(c_1968,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_2000,plain,
    ( v4_relat_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_2198,plain,
    ( ~ v1_partfun1(sK5,X0_53)
    | ~ v4_relat_1(sK5,X0_53)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = X0_53 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_2728,plain,
    ( ~ v1_partfun1(sK5,sK3)
    | ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_2198])).

cnf(c_5364,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5203,c_35,c_26,c_25,c_24,c_1968,c_2000,c_2384,c_2728])).

cnf(c_5368,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,sK3) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5364,c_1535])).

cnf(c_1969,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1968])).

cnf(c_6207,plain,
    ( r1_xboole_0(X0_53,sK3) != iProver_top
    | k7_relat_1(sK5,X0_53) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5368,c_49,c_1969])).

cnf(c_6208,plain,
    ( k7_relat_1(sK5,X0_53) = k1_xboole_0
    | r1_xboole_0(X0_53,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6207])).

cnf(c_6215,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3856,c_6208])).

cnf(c_2750,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_1540])).

cnf(c_2926,plain,
    ( k7_relat_1(sK5,k3_xboole_0(X0_53,X1_53)) = k7_relat_1(k7_relat_1(sK5,X0_53),X1_53) ),
    inference(superposition,[status(thm)],[c_2750,c_1534])).

cnf(c_6562,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK2,X0_53)) = k7_relat_1(k1_xboole_0,X0_53) ),
    inference(superposition,[status(thm)],[c_6215,c_2926])).

cnf(c_6610,plain,
    ( k7_relat_1(k1_xboole_0,sK3) = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3862,c_6562])).

cnf(c_23,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_664,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2416,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2248,c_664])).

cnf(c_3978,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3862,c_2416])).

cnf(c_5078,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5074,c_3978])).

cnf(c_5691,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5078,c_5080])).

cnf(c_6849,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_xboole_0,sK3) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_6610,c_5691])).

cnf(c_5702,plain,
    ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5696,c_1531])).

cnf(c_2838,plain,
    ( v4_relat_1(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1550,c_1541])).

cnf(c_3618,plain,
    ( k7_relat_1(sK5,sK3) = sK5
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2838,c_1536])).

cnf(c_2199,plain,
    ( ~ v4_relat_1(sK5,X0_53)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,X0_53) = sK5 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_2577,plain,
    ( ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,sK3) = sK5 ),
    inference(instantiation,[status(thm)],[c_2199])).

cnf(c_4193,plain,
    ( k7_relat_1(sK5,sK3) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3618,c_24,c_1968,c_2000,c_2577])).

cnf(c_4196,plain,
    ( k7_relat_1(sK5,k3_xboole_0(sK3,X0_53)) = k7_relat_1(sK5,X0_53) ),
    inference(superposition,[status(thm)],[c_4193,c_2926])).

cnf(c_6114,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2) ),
    inference(superposition,[status(thm)],[c_5702,c_4196])).

cnf(c_16095,plain,
    ( k7_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6114,c_6215,c_6610])).

cnf(c_17750,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6849,c_6606,c_16095])).

cnf(c_17751,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_17750])).

cnf(c_17752,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_17751,c_14443])).

cnf(c_16098,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_16095,c_6610])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_70328,c_59470,c_17752,c_16098,c_46,c_45,c_44,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:56:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 31.83/4.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.83/4.48  
% 31.83/4.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.83/4.48  
% 31.83/4.48  ------  iProver source info
% 31.83/4.48  
% 31.83/4.48  git: date: 2020-06-30 10:37:57 +0100
% 31.83/4.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.83/4.48  git: non_committed_changes: false
% 31.83/4.48  git: last_make_outside_of_git: false
% 31.83/4.48  
% 31.83/4.48  ------ 
% 31.83/4.48  ------ Parsing...
% 31.83/4.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.83/4.48  
% 31.83/4.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 31.83/4.48  
% 31.83/4.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.83/4.48  
% 31.83/4.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.83/4.48  ------ Proving...
% 31.83/4.48  ------ Problem Properties 
% 31.83/4.48  
% 31.83/4.48  
% 31.83/4.48  clauses                                 36
% 31.83/4.48  conjectures                             14
% 31.83/4.48  EPR                                     12
% 31.83/4.48  Horn                                    26
% 31.83/4.48  unary                                   13
% 31.83/4.48  binary                                  6
% 31.83/4.48  lits                                    148
% 31.83/4.48  lits eq                                 17
% 31.83/4.48  fd_pure                                 0
% 31.83/4.48  fd_pseudo                               0
% 31.83/4.48  fd_cond                                 0
% 31.83/4.48  fd_pseudo_cond                          1
% 31.83/4.48  AC symbols                              0
% 31.83/4.48  
% 31.83/4.48  ------ Input Options Time Limit: Unbounded
% 31.83/4.48  
% 31.83/4.48  
% 31.83/4.48  ------ 
% 31.83/4.48  Current options:
% 31.83/4.48  ------ 
% 31.83/4.48  
% 31.83/4.48  
% 31.83/4.48  
% 31.83/4.48  
% 31.83/4.48  ------ Proving...
% 31.83/4.48  
% 31.83/4.48  
% 31.83/4.48  % SZS status Theorem for theBenchmark.p
% 31.83/4.48  
% 31.83/4.48  % SZS output start CNFRefutation for theBenchmark.p
% 31.83/4.48  
% 31.83/4.48  fof(f16,conjecture,(
% 31.83/4.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f17,negated_conjecture,(
% 31.83/4.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 31.83/4.48    inference(negated_conjecture,[],[f16])).
% 31.83/4.48  
% 31.83/4.48  fof(f41,plain,(
% 31.83/4.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 31.83/4.48    inference(ennf_transformation,[],[f17])).
% 31.83/4.48  
% 31.83/4.48  fof(f42,plain,(
% 31.83/4.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 31.83/4.48    inference(flattening,[],[f41])).
% 31.83/4.48  
% 31.83/4.48  fof(f53,plain,(
% 31.83/4.48    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 31.83/4.48    introduced(choice_axiom,[])).
% 31.83/4.48  
% 31.83/4.48  fof(f52,plain,(
% 31.83/4.48    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 31.83/4.48    introduced(choice_axiom,[])).
% 31.83/4.48  
% 31.83/4.48  fof(f51,plain,(
% 31.83/4.48    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 31.83/4.48    introduced(choice_axiom,[])).
% 31.83/4.48  
% 31.83/4.48  fof(f50,plain,(
% 31.83/4.48    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 31.83/4.48    introduced(choice_axiom,[])).
% 31.83/4.48  
% 31.83/4.48  fof(f49,plain,(
% 31.83/4.48    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 31.83/4.48    introduced(choice_axiom,[])).
% 31.83/4.48  
% 31.83/4.48  fof(f48,plain,(
% 31.83/4.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 31.83/4.48    introduced(choice_axiom,[])).
% 31.83/4.48  
% 31.83/4.48  fof(f54,plain,(
% 31.83/4.48    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 31.83/4.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f42,f53,f52,f51,f50,f49,f48])).
% 31.83/4.48  
% 31.83/4.48  fof(f87,plain,(
% 31.83/4.48    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f13,axiom,(
% 31.83/4.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f35,plain,(
% 31.83/4.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 31.83/4.48    inference(ennf_transformation,[],[f13])).
% 31.83/4.48  
% 31.83/4.48  fof(f36,plain,(
% 31.83/4.48    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 31.83/4.48    inference(flattening,[],[f35])).
% 31.83/4.48  
% 31.83/4.48  fof(f71,plain,(
% 31.83/4.48    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f36])).
% 31.83/4.48  
% 31.83/4.48  fof(f85,plain,(
% 31.83/4.48    v1_funct_1(sK4)),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f83,plain,(
% 31.83/4.48    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f2,axiom,(
% 31.83/4.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f19,plain,(
% 31.83/4.48    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 31.83/4.48    inference(ennf_transformation,[],[f2])).
% 31.83/4.48  
% 31.83/4.48  fof(f57,plain,(
% 31.83/4.48    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 31.83/4.48    inference(cnf_transformation,[],[f19])).
% 31.83/4.48  
% 31.83/4.48  fof(f90,plain,(
% 31.83/4.48    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f88,plain,(
% 31.83/4.48    v1_funct_1(sK5)),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f14,axiom,(
% 31.83/4.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f37,plain,(
% 31.83/4.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 31.83/4.48    inference(ennf_transformation,[],[f14])).
% 31.83/4.48  
% 31.83/4.48  fof(f38,plain,(
% 31.83/4.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 31.83/4.48    inference(flattening,[],[f37])).
% 31.83/4.48  
% 31.83/4.48  fof(f46,plain,(
% 31.83/4.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 31.83/4.48    inference(nnf_transformation,[],[f38])).
% 31.83/4.48  
% 31.83/4.48  fof(f47,plain,(
% 31.83/4.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 31.83/4.48    inference(flattening,[],[f46])).
% 31.83/4.48  
% 31.83/4.48  fof(f73,plain,(
% 31.83/4.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f47])).
% 31.83/4.48  
% 31.83/4.48  fof(f95,plain,(
% 31.83/4.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.83/4.48    inference(equality_resolution,[],[f73])).
% 31.83/4.48  
% 31.83/4.48  fof(f15,axiom,(
% 31.83/4.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f39,plain,(
% 31.83/4.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 31.83/4.48    inference(ennf_transformation,[],[f15])).
% 31.83/4.48  
% 31.83/4.48  fof(f40,plain,(
% 31.83/4.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 31.83/4.48    inference(flattening,[],[f39])).
% 31.83/4.48  
% 31.83/4.48  fof(f75,plain,(
% 31.83/4.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f40])).
% 31.83/4.48  
% 31.83/4.48  fof(f76,plain,(
% 31.83/4.48    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f40])).
% 31.83/4.48  
% 31.83/4.48  fof(f77,plain,(
% 31.83/4.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f40])).
% 31.83/4.48  
% 31.83/4.48  fof(f3,axiom,(
% 31.83/4.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f20,plain,(
% 31.83/4.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 31.83/4.48    inference(ennf_transformation,[],[f3])).
% 31.83/4.48  
% 31.83/4.48  fof(f58,plain,(
% 31.83/4.48    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f20])).
% 31.83/4.48  
% 31.83/4.48  fof(f79,plain,(
% 31.83/4.48    ~v1_xboole_0(sK1)),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f82,plain,(
% 31.83/4.48    ~v1_xboole_0(sK3)),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f89,plain,(
% 31.83/4.48    v1_funct_2(sK5,sK3,sK1)),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f84,plain,(
% 31.83/4.48    r1_subset_1(sK2,sK3)),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f7,axiom,(
% 31.83/4.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f25,plain,(
% 31.83/4.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 31.83/4.48    inference(ennf_transformation,[],[f7])).
% 31.83/4.48  
% 31.83/4.48  fof(f26,plain,(
% 31.83/4.48    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 31.83/4.48    inference(flattening,[],[f25])).
% 31.83/4.48  
% 31.83/4.48  fof(f44,plain,(
% 31.83/4.48    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 31.83/4.48    inference(nnf_transformation,[],[f26])).
% 31.83/4.48  
% 31.83/4.48  fof(f62,plain,(
% 31.83/4.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f44])).
% 31.83/4.48  
% 31.83/4.48  fof(f80,plain,(
% 31.83/4.48    ~v1_xboole_0(sK2)),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f1,axiom,(
% 31.83/4.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f43,plain,(
% 31.83/4.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 31.83/4.48    inference(nnf_transformation,[],[f1])).
% 31.83/4.48  
% 31.83/4.48  fof(f55,plain,(
% 31.83/4.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f43])).
% 31.83/4.48  
% 31.83/4.48  fof(f8,axiom,(
% 31.83/4.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) => r1_subset_1(X1,X0)))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f27,plain,(
% 31.83/4.48    ! [X0,X1] : ((r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 31.83/4.48    inference(ennf_transformation,[],[f8])).
% 31.83/4.48  
% 31.83/4.48  fof(f28,plain,(
% 31.83/4.48    ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 31.83/4.48    inference(flattening,[],[f27])).
% 31.83/4.48  
% 31.83/4.48  fof(f64,plain,(
% 31.83/4.48    ( ! [X0,X1] : (r1_subset_1(X1,X0) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f28])).
% 31.83/4.48  
% 31.83/4.48  fof(f11,axiom,(
% 31.83/4.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f31,plain,(
% 31.83/4.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 31.83/4.48    inference(ennf_transformation,[],[f11])).
% 31.83/4.48  
% 31.83/4.48  fof(f32,plain,(
% 31.83/4.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 31.83/4.48    inference(flattening,[],[f31])).
% 31.83/4.48  
% 31.83/4.48  fof(f68,plain,(
% 31.83/4.48    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f32])).
% 31.83/4.48  
% 31.83/4.48  fof(f86,plain,(
% 31.83/4.48    v1_funct_2(sK4,sK2,sK1)),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f12,axiom,(
% 31.83/4.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f33,plain,(
% 31.83/4.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 31.83/4.48    inference(ennf_transformation,[],[f12])).
% 31.83/4.48  
% 31.83/4.48  fof(f34,plain,(
% 31.83/4.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.83/4.48    inference(flattening,[],[f33])).
% 31.83/4.48  
% 31.83/4.48  fof(f45,plain,(
% 31.83/4.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.83/4.48    inference(nnf_transformation,[],[f34])).
% 31.83/4.48  
% 31.83/4.48  fof(f69,plain,(
% 31.83/4.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f45])).
% 31.83/4.48  
% 31.83/4.48  fof(f9,axiom,(
% 31.83/4.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f29,plain,(
% 31.83/4.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.83/4.48    inference(ennf_transformation,[],[f9])).
% 31.83/4.48  
% 31.83/4.48  fof(f65,plain,(
% 31.83/4.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.83/4.48    inference(cnf_transformation,[],[f29])).
% 31.83/4.48  
% 31.83/4.48  fof(f10,axiom,(
% 31.83/4.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f18,plain,(
% 31.83/4.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 31.83/4.48    inference(pure_predicate_removal,[],[f10])).
% 31.83/4.48  
% 31.83/4.48  fof(f30,plain,(
% 31.83/4.48    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.83/4.48    inference(ennf_transformation,[],[f18])).
% 31.83/4.48  
% 31.83/4.48  fof(f66,plain,(
% 31.83/4.48    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.83/4.48    inference(cnf_transformation,[],[f30])).
% 31.83/4.48  
% 31.83/4.48  fof(f5,axiom,(
% 31.83/4.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f22,plain,(
% 31.83/4.48    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 31.83/4.48    inference(ennf_transformation,[],[f5])).
% 31.83/4.48  
% 31.83/4.48  fof(f60,plain,(
% 31.83/4.48    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f22])).
% 31.83/4.48  
% 31.83/4.48  fof(f6,axiom,(
% 31.83/4.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f23,plain,(
% 31.83/4.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 31.83/4.48    inference(ennf_transformation,[],[f6])).
% 31.83/4.48  
% 31.83/4.48  fof(f24,plain,(
% 31.83/4.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.83/4.48    inference(flattening,[],[f23])).
% 31.83/4.48  
% 31.83/4.48  fof(f61,plain,(
% 31.83/4.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f24])).
% 31.83/4.48  
% 31.83/4.48  fof(f4,axiom,(
% 31.83/4.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 31.83/4.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.83/4.48  
% 31.83/4.48  fof(f21,plain,(
% 31.83/4.48    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 31.83/4.48    inference(ennf_transformation,[],[f4])).
% 31.83/4.48  
% 31.83/4.48  fof(f59,plain,(
% 31.83/4.48    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f21])).
% 31.83/4.48  
% 31.83/4.48  fof(f81,plain,(
% 31.83/4.48    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  fof(f72,plain,(
% 31.83/4.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.83/4.48    inference(cnf_transformation,[],[f47])).
% 31.83/4.48  
% 31.83/4.48  fof(f96,plain,(
% 31.83/4.48    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 31.83/4.48    inference(equality_resolution,[],[f72])).
% 31.83/4.48  
% 31.83/4.48  fof(f91,plain,(
% 31.83/4.48    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 31.83/4.48    inference(cnf_transformation,[],[f54])).
% 31.83/4.48  
% 31.83/4.48  cnf(c_27,negated_conjecture,
% 31.83/4.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 31.83/4.48      inference(cnf_transformation,[],[f87]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_660,negated_conjecture,
% 31.83/4.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_27]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1553,plain,
% 31.83/4.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_16,plain,
% 31.83/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 31.83/4.48      inference(cnf_transformation,[],[f71]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_669,plain,
% 31.83/4.48      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 31.83/4.48      | ~ v1_funct_1(X0_53)
% 31.83/4.48      | k2_partfun1(X1_53,X2_53,X0_53,X3_53) = k7_relat_1(X0_53,X3_53) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_16]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1545,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,X1_53,X2_53,X3_53) = k7_relat_1(X2_53,X3_53)
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4660,plain,
% 31.83/4.48      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53)
% 31.83/4.48      | v1_funct_1(sK4) != iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1553,c_1545]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_29,negated_conjecture,
% 31.83/4.48      ( v1_funct_1(sK4) ),
% 31.83/4.48      inference(cnf_transformation,[],[f85]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2098,plain,
% 31.83/4.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 31.83/4.48      | ~ v1_funct_1(sK4)
% 31.83/4.48      | k2_partfun1(X0_53,X1_53,sK4,X2_53) = k7_relat_1(sK4,X2_53) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_669]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2379,plain,
% 31.83/4.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.83/4.48      | ~ v1_funct_1(sK4)
% 31.83/4.48      | k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_2098]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5080,plain,
% 31.83/4.48      ( k2_partfun1(sK2,sK1,sK4,X0_53) = k7_relat_1(sK4,X0_53) ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_4660,c_29,c_27,c_2379]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_31,negated_conjecture,
% 31.83/4.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 31.83/4.48      inference(cnf_transformation,[],[f83]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_656,negated_conjecture,
% 31.83/4.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_31]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1557,plain,
% 31.83/4.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2,plain,
% 31.83/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.83/4.48      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 31.83/4.48      inference(cnf_transformation,[],[f57]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_682,plain,
% 31.83/4.48      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 31.83/4.48      | k9_subset_1(X1_53,X2_53,X0_53) = k3_xboole_0(X2_53,X0_53) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_2]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1532,plain,
% 31.83/4.48      ( k9_subset_1(X0_53,X1_53,X2_53) = k3_xboole_0(X1_53,X2_53)
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2248,plain,
% 31.83/4.48      ( k9_subset_1(sK0,X0_53,sK3) = k3_xboole_0(X0_53,sK3) ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1557,c_1532]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_24,negated_conjecture,
% 31.83/4.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 31.83/4.48      inference(cnf_transformation,[],[f90]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_663,negated_conjecture,
% 31.83/4.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_24]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1550,plain,
% 31.83/4.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_663]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4659,plain,
% 31.83/4.48      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53)
% 31.83/4.48      | v1_funct_1(sK5) != iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1550,c_1545]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_26,negated_conjecture,
% 31.83/4.48      ( v1_funct_1(sK5) ),
% 31.83/4.48      inference(cnf_transformation,[],[f88]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2093,plain,
% 31.83/4.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 31.83/4.48      | ~ v1_funct_1(sK5)
% 31.83/4.48      | k2_partfun1(X0_53,X1_53,sK5,X2_53) = k7_relat_1(sK5,X2_53) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_669]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2374,plain,
% 31.83/4.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 31.83/4.48      | ~ v1_funct_1(sK5)
% 31.83/4.48      | k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_2093]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5074,plain,
% 31.83/4.48      ( k2_partfun1(sK3,sK1,sK5,X0_53) = k7_relat_1(sK5,X0_53) ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_4659,c_26,c_24,c_2374]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_18,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0,X1,X2)
% 31.83/4.48      | ~ v1_funct_2(X3,X4,X2)
% 31.83/4.48      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 31.83/4.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.83/4.48      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | ~ v1_funct_1(X3)
% 31.83/4.48      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 31.83/4.48      | v1_xboole_0(X5)
% 31.83/4.48      | v1_xboole_0(X2)
% 31.83/4.48      | v1_xboole_0(X4)
% 31.83/4.48      | v1_xboole_0(X1)
% 31.83/4.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 31.83/4.48      inference(cnf_transformation,[],[f95]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_22,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0,X1,X2)
% 31.83/4.48      | ~ v1_funct_2(X3,X4,X2)
% 31.83/4.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | ~ v1_funct_1(X3)
% 31.83/4.48      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 31.83/4.48      | v1_xboole_0(X5)
% 31.83/4.48      | v1_xboole_0(X2)
% 31.83/4.48      | v1_xboole_0(X4)
% 31.83/4.48      | v1_xboole_0(X1) ),
% 31.83/4.48      inference(cnf_transformation,[],[f75]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_21,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0,X1,X2)
% 31.83/4.48      | ~ v1_funct_2(X3,X4,X2)
% 31.83/4.48      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 31.83/4.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | ~ v1_funct_1(X3)
% 31.83/4.48      | v1_xboole_0(X5)
% 31.83/4.48      | v1_xboole_0(X2)
% 31.83/4.48      | v1_xboole_0(X4)
% 31.83/4.48      | v1_xboole_0(X1) ),
% 31.83/4.48      inference(cnf_transformation,[],[f76]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_20,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0,X1,X2)
% 31.83/4.48      | ~ v1_funct_2(X3,X4,X2)
% 31.83/4.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.83/4.48      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | ~ v1_funct_1(X3)
% 31.83/4.48      | v1_xboole_0(X5)
% 31.83/4.48      | v1_xboole_0(X2)
% 31.83/4.48      | v1_xboole_0(X4)
% 31.83/4.48      | v1_xboole_0(X1) ),
% 31.83/4.48      inference(cnf_transformation,[],[f77]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_380,plain,
% 31.83/4.48      ( ~ v1_funct_1(X3)
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | ~ v1_funct_2(X3,X4,X2)
% 31.83/4.48      | ~ v1_funct_2(X0,X1,X2)
% 31.83/4.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.83/4.48      | v1_xboole_0(X5)
% 31.83/4.48      | v1_xboole_0(X2)
% 31.83/4.48      | v1_xboole_0(X4)
% 31.83/4.48      | v1_xboole_0(X1)
% 31.83/4.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_18,c_22,c_21,c_20]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_381,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0,X1,X2)
% 31.83/4.48      | ~ v1_funct_2(X3,X4,X2)
% 31.83/4.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | ~ v1_funct_1(X3)
% 31.83/4.48      | v1_xboole_0(X1)
% 31.83/4.48      | v1_xboole_0(X2)
% 31.83/4.48      | v1_xboole_0(X4)
% 31.83/4.48      | v1_xboole_0(X5)
% 31.83/4.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 31.83/4.48      inference(renaming,[status(thm)],[c_380]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_649,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 31.83/4.48      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 31.83/4.48      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 31.83/4.48      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 31.83/4.48      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 31.83/4.48      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 31.83/4.48      | ~ v1_funct_1(X0_53)
% 31.83/4.48      | ~ v1_funct_1(X3_53)
% 31.83/4.48      | v1_xboole_0(X1_53)
% 31.83/4.48      | v1_xboole_0(X2_53)
% 31.83/4.48      | v1_xboole_0(X4_53)
% 31.83/4.48      | v1_xboole_0(X5_53)
% 31.83/4.48      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X1_53) = X0_53 ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_381]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1564,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X0_53) = X2_53
% 31.83/4.48      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X5_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X3_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X4_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_649]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_3,plain,
% 31.83/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.83/4.48      | ~ v1_xboole_0(X1)
% 31.83/4.48      | v1_xboole_0(X0) ),
% 31.83/4.48      inference(cnf_transformation,[],[f58]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_681,plain,
% 31.83/4.48      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 31.83/4.48      | ~ v1_xboole_0(X1_53)
% 31.83/4.48      | v1_xboole_0(X0_53) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_3]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1533,plain,
% 31.83/4.48      ( m1_subset_1(X0_53,k1_zfmisc_1(X1_53)) != iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1813,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X4_53) = X5_53
% 31.83/4.48      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 31.83/4.48      | v1_funct_1(X5_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X4_53) = iProver_top ),
% 31.83/4.48      inference(forward_subsumption_resolution,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_1564,c_1533]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_10245,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_funct_1(sK5) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK1) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5074,c_1813]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_35,negated_conjecture,
% 31.83/4.48      ( ~ v1_xboole_0(sK1) ),
% 31.83/4.48      inference(cnf_transformation,[],[f79]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_38,plain,
% 31.83/4.48      ( v1_xboole_0(sK1) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_32,negated_conjecture,
% 31.83/4.48      ( ~ v1_xboole_0(sK3) ),
% 31.83/4.48      inference(cnf_transformation,[],[f82]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_41,plain,
% 31.83/4.48      ( v1_xboole_0(sK3) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_47,plain,
% 31.83/4.48      ( v1_funct_1(sK5) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_25,negated_conjecture,
% 31.83/4.48      ( v1_funct_2(sK5,sK3,sK1) ),
% 31.83/4.48      inference(cnf_transformation,[],[f89]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_48,plain,
% 31.83/4.48      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_49,plain,
% 31.83/4.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_52419,plain,
% 31.83/4.48      ( v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 31.83/4.48      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_10245,c_38,c_41,c_47,c_48,c_49]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_52420,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(renaming,[status(thm)],[c_52419]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_52439,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_2248,c_52420]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_52448,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(light_normalisation,[status(thm)],[c_52439,c_2248]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_42,plain,
% 31.83/4.48      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_70225,plain,
% 31.83/4.48      ( m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 31.83/4.48      | k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_52448,c_38,c_47,c_48,c_49,c_56479]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_70226,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),sK3) = sK5
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(renaming,[status(thm)],[c_70225]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_70239,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 31.83/4.48      | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
% 31.83/4.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(sK4) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5080,c_70226]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_30,negated_conjecture,
% 31.83/4.48      ( r1_subset_1(sK2,sK3) ),
% 31.83/4.48      inference(cnf_transformation,[],[f84]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_657,negated_conjecture,
% 31.83/4.48      ( r1_subset_1(sK2,sK3) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_30]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1556,plain,
% 31.83/4.48      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_8,plain,
% 31.83/4.48      ( ~ r1_subset_1(X0,X1)
% 31.83/4.48      | r1_xboole_0(X0,X1)
% 31.83/4.48      | v1_xboole_0(X0)
% 31.83/4.48      | v1_xboole_0(X1) ),
% 31.83/4.48      inference(cnf_transformation,[],[f62]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_676,plain,
% 31.83/4.48      ( ~ r1_subset_1(X0_53,X1_53)
% 31.83/4.48      | r1_xboole_0(X0_53,X1_53)
% 31.83/4.48      | v1_xboole_0(X1_53)
% 31.83/4.48      | v1_xboole_0(X0_53) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_8]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1538,plain,
% 31.83/4.48      ( r1_subset_1(X0_53,X1_53) != iProver_top
% 31.83/4.48      | r1_xboole_0(X0_53,X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_3853,plain,
% 31.83/4.48      ( r1_xboole_0(sK2,sK3) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1556,c_1538]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_34,negated_conjecture,
% 31.83/4.48      ( ~ v1_xboole_0(sK2) ),
% 31.83/4.48      inference(cnf_transformation,[],[f80]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_39,plain,
% 31.83/4.48      ( v1_xboole_0(sK2) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_43,plain,
% 31.83/4.48      ( r1_subset_1(sK2,sK3) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2009,plain,
% 31.83/4.48      ( ~ r1_subset_1(sK2,sK3)
% 31.83/4.48      | r1_xboole_0(sK2,sK3)
% 31.83/4.48      | v1_xboole_0(sK3)
% 31.83/4.48      | v1_xboole_0(sK2) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_676]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2010,plain,
% 31.83/4.48      ( r1_subset_1(sK2,sK3) != iProver_top
% 31.83/4.48      | r1_xboole_0(sK2,sK3) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_2009]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_3856,plain,
% 31.83/4.48      ( r1_xboole_0(sK2,sK3) = iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_3853,c_39,c_41,c_43,c_2010]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1,plain,
% 31.83/4.48      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 31.83/4.48      inference(cnf_transformation,[],[f55]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_683,plain,
% 31.83/4.48      ( ~ r1_xboole_0(X0_53,X1_53)
% 31.83/4.48      | k3_xboole_0(X0_53,X1_53) = k1_xboole_0 ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_1]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1531,plain,
% 31.83/4.48      ( k3_xboole_0(X0_53,X1_53) = k1_xboole_0
% 31.83/4.48      | r1_xboole_0(X0_53,X1_53) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_3862,plain,
% 31.83/4.48      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_3856,c_1531]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_9,plain,
% 31.83/4.48      ( ~ r1_subset_1(X0,X1)
% 31.83/4.48      | r1_subset_1(X1,X0)
% 31.83/4.48      | v1_xboole_0(X0)
% 31.83/4.48      | v1_xboole_0(X1) ),
% 31.83/4.48      inference(cnf_transformation,[],[f64]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_675,plain,
% 31.83/4.48      ( ~ r1_subset_1(X0_53,X1_53)
% 31.83/4.48      | r1_subset_1(X1_53,X0_53)
% 31.83/4.48      | v1_xboole_0(X1_53)
% 31.83/4.48      | v1_xboole_0(X0_53) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_9]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1539,plain,
% 31.83/4.48      ( r1_subset_1(X0_53,X1_53) != iProver_top
% 31.83/4.48      | r1_subset_1(X1_53,X0_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4527,plain,
% 31.83/4.48      ( r1_subset_1(sK3,sK2) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1556,c_1539]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2006,plain,
% 31.83/4.48      ( r1_subset_1(sK3,sK2)
% 31.83/4.48      | ~ r1_subset_1(sK2,sK3)
% 31.83/4.48      | v1_xboole_0(sK3)
% 31.83/4.48      | v1_xboole_0(sK2) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_675]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2007,plain,
% 31.83/4.48      ( r1_subset_1(sK3,sK2) = iProver_top
% 31.83/4.48      | r1_subset_1(sK2,sK3) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_2006]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4828,plain,
% 31.83/4.48      ( r1_subset_1(sK3,sK2) = iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_4527,c_39,c_41,c_43,c_2007]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4834,plain,
% 31.83/4.48      ( r1_xboole_0(sK3,sK2) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_4828,c_1538]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2236,plain,
% 31.83/4.48      ( ~ r1_subset_1(sK3,sK2)
% 31.83/4.48      | r1_xboole_0(sK3,sK2)
% 31.83/4.48      | v1_xboole_0(sK3)
% 31.83/4.48      | v1_xboole_0(sK2) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_676]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2238,plain,
% 31.83/4.48      ( r1_subset_1(sK3,sK2) != iProver_top
% 31.83/4.48      | r1_xboole_0(sK3,sK2) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_2236]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5696,plain,
% 31.83/4.48      ( r1_xboole_0(sK3,sK2) = iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_4834,c_39,c_41,c_43,c_2007,c_2238]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_12,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0,X1,X2)
% 31.83/4.48      | v1_partfun1(X0,X1)
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | v1_xboole_0(X2) ),
% 31.83/4.48      inference(cnf_transformation,[],[f68]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_672,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 31.83/4.48      | v1_partfun1(X0_53,X1_53)
% 31.83/4.48      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 31.83/4.48      | ~ v1_funct_1(X0_53)
% 31.83/4.48      | v1_xboole_0(X2_53) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_12]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1542,plain,
% 31.83/4.48      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 31.83/4.48      | v1_partfun1(X0_53,X1_53) = iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 31.83/4.48      | v1_funct_1(X0_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X2_53) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4808,plain,
% 31.83/4.48      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.83/4.48      | v1_partfun1(sK4,sK2) = iProver_top
% 31.83/4.48      | v1_funct_1(sK4) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK1) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1553,c_1542]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_44,plain,
% 31.83/4.48      ( v1_funct_1(sK4) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_28,negated_conjecture,
% 31.83/4.48      ( v1_funct_2(sK4,sK2,sK1) ),
% 31.83/4.48      inference(cnf_transformation,[],[f86]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_45,plain,
% 31.83/4.48      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_46,plain,
% 31.83/4.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2108,plain,
% 31.83/4.48      ( ~ v1_funct_2(sK4,X0_53,X1_53)
% 31.83/4.48      | v1_partfun1(sK4,X0_53)
% 31.83/4.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 31.83/4.48      | ~ v1_funct_1(sK4)
% 31.83/4.48      | v1_xboole_0(X1_53) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_672]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2387,plain,
% 31.83/4.48      ( ~ v1_funct_2(sK4,sK2,sK1)
% 31.83/4.48      | v1_partfun1(sK4,sK2)
% 31.83/4.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.83/4.48      | ~ v1_funct_1(sK4)
% 31.83/4.48      | v1_xboole_0(sK1) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_2108]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2388,plain,
% 31.83/4.48      ( v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.83/4.48      | v1_partfun1(sK4,sK2) = iProver_top
% 31.83/4.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.83/4.48      | v1_funct_1(sK4) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK1) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_2387]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5206,plain,
% 31.83/4.48      ( v1_partfun1(sK4,sK2) = iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_4808,c_38,c_44,c_45,c_46,c_2388]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_15,plain,
% 31.83/4.48      ( ~ v1_partfun1(X0,X1)
% 31.83/4.48      | ~ v4_relat_1(X0,X1)
% 31.83/4.48      | ~ v1_relat_1(X0)
% 31.83/4.48      | k1_relat_1(X0) = X1 ),
% 31.83/4.48      inference(cnf_transformation,[],[f69]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_670,plain,
% 31.83/4.48      ( ~ v1_partfun1(X0_53,X1_53)
% 31.83/4.48      | ~ v4_relat_1(X0_53,X1_53)
% 31.83/4.48      | ~ v1_relat_1(X0_53)
% 31.83/4.48      | k1_relat_1(X0_53) = X1_53 ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_15]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1544,plain,
% 31.83/4.48      ( k1_relat_1(X0_53) = X1_53
% 31.83/4.48      | v1_partfun1(X0_53,X1_53) != iProver_top
% 31.83/4.48      | v4_relat_1(X0_53,X1_53) != iProver_top
% 31.83/4.48      | v1_relat_1(X0_53) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_670]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5211,plain,
% 31.83/4.48      ( k1_relat_1(sK4) = sK2
% 31.83/4.48      | v4_relat_1(sK4,sK2) != iProver_top
% 31.83/4.48      | v1_relat_1(sK4) != iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5206,c_1544]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_10,plain,
% 31.83/4.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | v1_relat_1(X0) ),
% 31.83/4.48      inference(cnf_transformation,[],[f65]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_674,plain,
% 31.83/4.48      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 31.83/4.48      | v1_relat_1(X0_53) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_10]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1971,plain,
% 31.83/4.48      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.83/4.48      | v1_relat_1(sK4) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_674]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_11,plain,
% 31.83/4.48      ( v4_relat_1(X0,X1)
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 31.83/4.48      inference(cnf_transformation,[],[f66]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_673,plain,
% 31.83/4.48      ( v4_relat_1(X0_53,X1_53)
% 31.83/4.48      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_11]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2003,plain,
% 31.83/4.48      ( v4_relat_1(sK4,sK2)
% 31.83/4.48      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_673]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2213,plain,
% 31.83/4.48      ( ~ v1_partfun1(sK4,X0_53)
% 31.83/4.48      | ~ v4_relat_1(sK4,X0_53)
% 31.83/4.48      | ~ v1_relat_1(sK4)
% 31.83/4.48      | k1_relat_1(sK4) = X0_53 ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_670]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2220,plain,
% 31.83/4.48      ( ~ v1_partfun1(sK4,sK2)
% 31.83/4.48      | ~ v4_relat_1(sK4,sK2)
% 31.83/4.48      | ~ v1_relat_1(sK4)
% 31.83/4.48      | k1_relat_1(sK4) = sK2 ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_2213]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5383,plain,
% 31.83/4.48      ( k1_relat_1(sK4) = sK2 ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_5211,c_35,c_29,c_28,c_27,c_1971,c_2003,c_2220,c_2387]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5,plain,
% 31.83/4.48      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 31.83/4.48      | ~ v1_relat_1(X1)
% 31.83/4.48      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 31.83/4.48      inference(cnf_transformation,[],[f60]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_679,plain,
% 31.83/4.48      ( ~ r1_xboole_0(X0_53,k1_relat_1(X1_53))
% 31.83/4.48      | ~ v1_relat_1(X1_53)
% 31.83/4.48      | k7_relat_1(X1_53,X0_53) = k1_xboole_0 ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_5]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1535,plain,
% 31.83/4.48      ( k7_relat_1(X0_53,X1_53) = k1_xboole_0
% 31.83/4.48      | r1_xboole_0(X1_53,k1_relat_1(X0_53)) != iProver_top
% 31.83/4.48      | v1_relat_1(X0_53) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5387,plain,
% 31.83/4.48      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 31.83/4.48      | r1_xboole_0(X0_53,sK2) != iProver_top
% 31.83/4.48      | v1_relat_1(sK4) != iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5383,c_1535]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1972,plain,
% 31.83/4.48      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.83/4.48      | v1_relat_1(sK4) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_1971]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6217,plain,
% 31.83/4.48      ( r1_xboole_0(X0_53,sK2) != iProver_top
% 31.83/4.48      | k7_relat_1(sK4,X0_53) = k1_xboole_0 ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_5387,c_46,c_1972]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6218,plain,
% 31.83/4.48      ( k7_relat_1(sK4,X0_53) = k1_xboole_0
% 31.83/4.48      | r1_xboole_0(X0_53,sK2) != iProver_top ),
% 31.83/4.48      inference(renaming,[status(thm)],[c_6217]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6225,plain,
% 31.83/4.48      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5696,c_6218]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1541,plain,
% 31.83/4.48      ( v4_relat_1(X0_53,X1_53) = iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2839,plain,
% 31.83/4.48      ( v4_relat_1(sK4,sK2) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1553,c_1541]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6,plain,
% 31.83/4.48      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 31.83/4.48      inference(cnf_transformation,[],[f61]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_678,plain,
% 31.83/4.48      ( ~ v4_relat_1(X0_53,X1_53)
% 31.83/4.48      | ~ v1_relat_1(X0_53)
% 31.83/4.48      | k7_relat_1(X0_53,X1_53) = X0_53 ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_6]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1536,plain,
% 31.83/4.48      ( k7_relat_1(X0_53,X1_53) = X0_53
% 31.83/4.48      | v4_relat_1(X0_53,X1_53) != iProver_top
% 31.83/4.48      | v1_relat_1(X0_53) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_3619,plain,
% 31.83/4.48      ( k7_relat_1(sK4,sK2) = sK4 | v1_relat_1(sK4) != iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_2839,c_1536]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2214,plain,
% 31.83/4.48      ( ~ v4_relat_1(sK4,X0_53)
% 31.83/4.48      | ~ v1_relat_1(sK4)
% 31.83/4.48      | k7_relat_1(sK4,X0_53) = sK4 ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_678]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2216,plain,
% 31.83/4.48      ( ~ v4_relat_1(sK4,sK2)
% 31.83/4.48      | ~ v1_relat_1(sK4)
% 31.83/4.48      | k7_relat_1(sK4,sK2) = sK4 ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_2214]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4199,plain,
% 31.83/4.48      ( k7_relat_1(sK4,sK2) = sK4 ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_3619,c_27,c_1971,c_2003,c_2216]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1540,plain,
% 31.83/4.48      ( m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 31.83/4.48      | v1_relat_1(X0_53) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2751,plain,
% 31.83/4.48      ( v1_relat_1(sK4) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1553,c_1540]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4,plain,
% 31.83/4.48      ( ~ v1_relat_1(X0)
% 31.83/4.48      | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,k3_xboole_0(X1,X2)) ),
% 31.83/4.48      inference(cnf_transformation,[],[f59]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_680,plain,
% 31.83/4.48      ( ~ v1_relat_1(X0_53)
% 31.83/4.48      | k7_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53)) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_4]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1534,plain,
% 31.83/4.48      ( k7_relat_1(k7_relat_1(X0_53,X1_53),X2_53) = k7_relat_1(X0_53,k3_xboole_0(X1_53,X2_53))
% 31.83/4.48      | v1_relat_1(X0_53) != iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2930,plain,
% 31.83/4.48      ( k7_relat_1(sK4,k3_xboole_0(X0_53,X1_53)) = k7_relat_1(k7_relat_1(sK4,X0_53),X1_53) ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_2751,c_1534]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4202,plain,
% 31.83/4.48      ( k7_relat_1(sK4,k3_xboole_0(sK2,X0_53)) = k7_relat_1(sK4,X0_53) ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_4199,c_2930]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4325,plain,
% 31.83/4.48      ( k7_relat_1(sK4,sK3) = k7_relat_1(sK4,k1_xboole_0) ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_3862,c_4202]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6606,plain,
% 31.83/4.48      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 31.83/4.48      inference(demodulation,[status(thm)],[c_6225,c_4325]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_70327,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 31.83/4.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 31.83/4.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(sK4) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(light_normalisation,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_70239,c_3862,c_6606]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_667,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 31.83/4.48      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 31.83/4.48      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 31.83/4.48      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 31.83/4.48      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 31.83/4.48      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 31.83/4.48      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53)))
% 31.83/4.48      | ~ v1_funct_1(X0_53)
% 31.83/4.48      | ~ v1_funct_1(X3_53)
% 31.83/4.48      | v1_xboole_0(X1_53)
% 31.83/4.48      | v1_xboole_0(X2_53)
% 31.83/4.48      | v1_xboole_0(X4_53)
% 31.83/4.48      | v1_xboole_0(X5_53) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_20]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1547,plain,
% 31.83/4.48      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 31.83/4.48      | v1_funct_1(X0_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X3_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X5_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X2_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X4_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1758,plain,
% 31.83/4.48      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_53,X4_53,X1_53),X2_53))) = iProver_top
% 31.83/4.48      | v1_funct_1(X0_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X3_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X2_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X4_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top ),
% 31.83/4.48      inference(forward_subsumption_resolution,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_1547,c_1533]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_7266,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 31.83/4.48      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 31.83/4.48      | v1_funct_1(X5_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X4_53) != iProver_top
% 31.83/4.48      | v1_funct_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53)) != iProver_top
% 31.83/4.48      | v1_xboole_0(X3_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X2_53) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1758,c_1545]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_665,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 31.83/4.48      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 31.83/4.48      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 31.83/4.48      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 31.83/4.48      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 31.83/4.48      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 31.83/4.48      | ~ v1_funct_1(X0_53)
% 31.83/4.48      | ~ v1_funct_1(X3_53)
% 31.83/4.48      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53))
% 31.83/4.48      | v1_xboole_0(X1_53)
% 31.83/4.48      | v1_xboole_0(X2_53)
% 31.83/4.48      | v1_xboole_0(X4_53)
% 31.83/4.48      | v1_xboole_0(X5_53) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_22]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1549,plain,
% 31.83/4.48      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 31.83/4.48      | v1_funct_1(X0_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X3_53) != iProver_top
% 31.83/4.48      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 31.83/4.48      | v1_xboole_0(X5_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X2_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X4_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1706,plain,
% 31.83/4.48      ( v1_funct_2(X0_53,X1_53,X2_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X3_53,X4_53,X2_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X4_53,k1_zfmisc_1(X5_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(X5_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53))) != iProver_top
% 31.83/4.48      | v1_funct_1(X0_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X3_53) != iProver_top
% 31.83/4.48      | v1_funct_1(k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53)) = iProver_top
% 31.83/4.48      | v1_xboole_0(X2_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X4_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top ),
% 31.83/4.48      inference(forward_subsumption_resolution,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_1549,c_1533]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_13023,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(X0_53,X1_53,X2_53),X3_53,k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53) = k7_relat_1(k1_tmap_1(X0_53,X3_53,X1_53,X2_53,X4_53,X5_53),X6_53)
% 31.83/4.48      | v1_funct_2(X5_53,X2_53,X3_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X4_53,X1_53,X3_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X4_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X3_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X2_53,X3_53))) != iProver_top
% 31.83/4.48      | v1_funct_1(X5_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X4_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X2_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X3_53) = iProver_top ),
% 31.83/4.48      inference(forward_subsumption_resolution,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_7266,c_1706]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_13028,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(X0_53,sK2,X1_53),sK1,k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53)
% 31.83/4.48      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 31.83/4.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | v1_funct_1(sK4) != iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK1) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1553,c_13023]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_13899,plain,
% 31.83/4.48      ( v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | k2_partfun1(k4_subset_1(X0_53,sK2,X1_53),sK1,k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53)
% 31.83/4.48      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_13028,c_38,c_39,c_44,c_45]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_13900,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(X0_53,sK2,X1_53),sK1,k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,X1_53,sK4,X2_53),X3_53)
% 31.83/4.48      | v1_funct_2(X2_53,X1_53,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top ),
% 31.83/4.48      inference(renaming,[status(thm)],[c_13899]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_13912,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 31.83/4.48      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | v1_funct_1(sK5) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1550,c_13900]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_14429,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(X0_53,sK2,sK3),sK1,k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53) = k7_relat_1(k1_tmap_1(X0_53,sK1,sK2,sK3,sK4,sK5),X1_53)
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(X0_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(X0_53)) != iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_13912,c_41,c_47,c_48]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_14438,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53)
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1557,c_14429]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_33,negated_conjecture,
% 31.83/4.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 31.83/4.48      inference(cnf_transformation,[],[f81]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_40,plain,
% 31.83/4.48      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_14443,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_53) ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_14438,c_40]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_70328,plain,
% 31.83/4.48      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 31.83/4.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 31.83/4.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(sK4) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(demodulation,[status(thm)],[c_70327,c_14443]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_19,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0,X1,X2)
% 31.83/4.48      | ~ v1_funct_2(X3,X4,X2)
% 31.83/4.48      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 31.83/4.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.83/4.48      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | ~ v1_funct_1(X3)
% 31.83/4.48      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 31.83/4.48      | v1_xboole_0(X5)
% 31.83/4.48      | v1_xboole_0(X2)
% 31.83/4.48      | v1_xboole_0(X4)
% 31.83/4.48      | v1_xboole_0(X1)
% 31.83/4.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 31.83/4.48      inference(cnf_transformation,[],[f96]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_371,plain,
% 31.83/4.48      ( ~ v1_funct_1(X3)
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | ~ v1_funct_2(X3,X4,X2)
% 31.83/4.48      | ~ v1_funct_2(X0,X1,X2)
% 31.83/4.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.83/4.48      | v1_xboole_0(X5)
% 31.83/4.48      | v1_xboole_0(X2)
% 31.83/4.48      | v1_xboole_0(X4)
% 31.83/4.48      | v1_xboole_0(X1)
% 31.83/4.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_19,c_22,c_21,c_20]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_372,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0,X1,X2)
% 31.83/4.48      | ~ v1_funct_2(X3,X4,X2)
% 31.83/4.48      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 31.83/4.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.83/4.48      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.83/4.48      | ~ v1_funct_1(X0)
% 31.83/4.48      | ~ v1_funct_1(X3)
% 31.83/4.48      | v1_xboole_0(X1)
% 31.83/4.48      | v1_xboole_0(X2)
% 31.83/4.48      | v1_xboole_0(X4)
% 31.83/4.48      | v1_xboole_0(X5)
% 31.83/4.48      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 31.83/4.48      inference(renaming,[status(thm)],[c_371]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_650,plain,
% 31.83/4.48      ( ~ v1_funct_2(X0_53,X1_53,X2_53)
% 31.83/4.48      | ~ v1_funct_2(X3_53,X4_53,X2_53)
% 31.83/4.48      | ~ m1_subset_1(X4_53,k1_zfmisc_1(X5_53))
% 31.83/4.48      | ~ m1_subset_1(X1_53,k1_zfmisc_1(X5_53))
% 31.83/4.48      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X1_53,X2_53)))
% 31.83/4.48      | ~ m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X2_53)))
% 31.83/4.48      | ~ v1_funct_1(X0_53)
% 31.83/4.48      | ~ v1_funct_1(X3_53)
% 31.83/4.48      | v1_xboole_0(X1_53)
% 31.83/4.48      | v1_xboole_0(X2_53)
% 31.83/4.48      | v1_xboole_0(X4_53)
% 31.83/4.48      | v1_xboole_0(X5_53)
% 31.83/4.48      | k2_partfun1(X1_53,X2_53,X0_53,k9_subset_1(X5_53,X4_53,X1_53)) != k2_partfun1(X4_53,X2_53,X3_53,k9_subset_1(X5_53,X4_53,X1_53))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X5_53,X4_53,X1_53),X2_53,k1_tmap_1(X5_53,X2_53,X4_53,X1_53,X3_53,X0_53),X4_53) = X3_53 ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_372]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1563,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X4_53,X0_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X4_53,X0_53))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X3_53,X4_53,X0_53),X1_53,k1_tmap_1(X3_53,X1_53,X4_53,X0_53,X5_53,X2_53),X4_53) = X5_53
% 31.83/4.48      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X5_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X3_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X4_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1785,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(X3_53,X0_53,X4_53)) != k2_partfun1(X4_53,X1_53,X5_53,k9_subset_1(X3_53,X0_53,X4_53))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X3_53,X0_53,X4_53),X1_53,k1_tmap_1(X3_53,X1_53,X0_53,X4_53,X2_53,X5_53),X0_53) = X2_53
% 31.83/4.48      | v1_funct_2(X5_53,X4_53,X1_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(X3_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X4_53,k1_zfmisc_1(X3_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X5_53,k1_zfmisc_1(k2_zfmisc_1(X4_53,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 31.83/4.48      | v1_funct_1(X5_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X4_53) = iProver_top ),
% 31.83/4.48      inference(forward_subsumption_resolution,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_1563,c_1533]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_8467,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_funct_1(sK5) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK1) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5074,c_1785]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_28843,plain,
% 31.83/4.48      ( v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 31.83/4.48      | k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_8467,c_38,c_41,c_47,c_48,c_49]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_28844,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k9_subset_1(X2_53,X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_53,X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(X2_53,X0_53,sK3),sK1,k1_tmap_1(X2_53,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(X2_53)) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(renaming,[status(thm)],[c_28843]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_28863,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_2248,c_28844]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_28872,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(light_normalisation,[status(thm)],[c_28863,c_2248]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_8471,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,X1_53,X2_53,k9_subset_1(sK0,X0_53,sK3)) != k2_partfun1(sK3,X1_53,X3_53,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),X1_53,k1_tmap_1(sK0,X1_53,X0_53,sK3,X2_53,X3_53),X0_53) = X2_53
% 31.83/4.48      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X3_53,sK3,X1_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X3_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_2248,c_1785]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_8528,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,X1_53,X2_53,k3_xboole_0(X0_53,sK3)) != k2_partfun1(sK3,X1_53,X3_53,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),X1_53,k1_tmap_1(sK0,X1_53,X0_53,sK3,X2_53,X3_53),X0_53) = X2_53
% 31.83/4.48      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X3_53,sK3,X1_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(X3_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK3) = iProver_top ),
% 31.83/4.48      inference(light_normalisation,[status(thm)],[c_8471,c_2248]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_33948,plain,
% 31.83/4.48      ( v1_xboole_0(X0_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X3_53) != iProver_top
% 31.83/4.48      | k2_partfun1(X0_53,X1_53,X2_53,k3_xboole_0(X0_53,sK3)) != k2_partfun1(sK3,X1_53,X3_53,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),X1_53,k1_tmap_1(sK0,X1_53,X0_53,sK3,X2_53,X3_53),X0_53) = X2_53
% 31.83/4.48      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X3_53,sK3,X1_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_8528,c_41,c_42]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_33949,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,X1_53,X2_53,k3_xboole_0(X0_53,sK3)) != k2_partfun1(sK3,X1_53,X3_53,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),X1_53,k1_tmap_1(sK0,X1_53,X0_53,sK3,X2_53,X3_53),X0_53) = X2_53
% 31.83/4.48      | v1_funct_2(X2_53,X0_53,X1_53) != iProver_top
% 31.83/4.48      | v1_funct_2(X3_53,sK3,X1_53) != iProver_top
% 31.83/4.48      | m1_subset_1(X2_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X3_53,k1_zfmisc_1(k2_zfmisc_1(sK3,X1_53))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(X3_53) != iProver_top
% 31.83/4.48      | v1_funct_1(X2_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X1_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(renaming,[status(thm)],[c_33948]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_33971,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_funct_1(sK5) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top
% 31.83/4.48      | v1_xboole_0(sK1) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5074,c_33949]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_59367,plain,
% 31.83/4.48      ( m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 31.83/4.48      | k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_28872,c_42]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_59368,plain,
% 31.83/4.48      ( k2_partfun1(X0_53,sK1,X1_53,k3_xboole_0(X0_53,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_53,sK3))
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,X0_53,sK3),sK1,k1_tmap_1(sK0,sK1,X0_53,sK3,X1_53,sK5),X0_53) = X1_53
% 31.83/4.48      | v1_funct_2(X1_53,X0_53,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(X1_53,k1_zfmisc_1(k2_zfmisc_1(X0_53,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(X0_53,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(X1_53) != iProver_top
% 31.83/4.48      | v1_xboole_0(X0_53) = iProver_top ),
% 31.83/4.48      inference(renaming,[status(thm)],[c_59367]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_59381,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 31.83/4.48      | k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
% 31.83/4.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(sK4) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5080,c_59368]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_59469,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 31.83/4.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 31.83/4.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(sK4) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(light_normalisation,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_59381,c_3862,c_6606]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_59470,plain,
% 31.83/4.48      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 31.83/4.48      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 31.83/4.48      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.83/4.48      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.83/4.48      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 31.83/4.48      | v1_funct_1(sK4) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK2) = iProver_top ),
% 31.83/4.48      inference(demodulation,[status(thm)],[c_59469,c_14443]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4807,plain,
% 31.83/4.48      ( v1_funct_2(sK5,sK3,sK1) != iProver_top
% 31.83/4.48      | v1_partfun1(sK5,sK3) = iProver_top
% 31.83/4.48      | v1_funct_1(sK5) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK1) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1550,c_1542]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2103,plain,
% 31.83/4.48      ( ~ v1_funct_2(sK5,X0_53,X1_53)
% 31.83/4.48      | v1_partfun1(sK5,X0_53)
% 31.83/4.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 31.83/4.48      | ~ v1_funct_1(sK5)
% 31.83/4.48      | v1_xboole_0(X1_53) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_672]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2384,plain,
% 31.83/4.48      ( ~ v1_funct_2(sK5,sK3,sK1)
% 31.83/4.48      | v1_partfun1(sK5,sK3)
% 31.83/4.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 31.83/4.48      | ~ v1_funct_1(sK5)
% 31.83/4.48      | v1_xboole_0(sK1) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_2103]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2385,plain,
% 31.83/4.48      ( v1_funct_2(sK5,sK3,sK1) != iProver_top
% 31.83/4.48      | v1_partfun1(sK5,sK3) = iProver_top
% 31.83/4.48      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 31.83/4.48      | v1_funct_1(sK5) != iProver_top
% 31.83/4.48      | v1_xboole_0(sK1) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_2384]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5198,plain,
% 31.83/4.48      ( v1_partfun1(sK5,sK3) = iProver_top ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_4807,c_38,c_47,c_48,c_49,c_2385]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5203,plain,
% 31.83/4.48      ( k1_relat_1(sK5) = sK3
% 31.83/4.48      | v4_relat_1(sK5,sK3) != iProver_top
% 31.83/4.48      | v1_relat_1(sK5) != iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5198,c_1544]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1968,plain,
% 31.83/4.48      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 31.83/4.48      | v1_relat_1(sK5) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_674]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2000,plain,
% 31.83/4.48      ( v4_relat_1(sK5,sK3)
% 31.83/4.48      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_673]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2198,plain,
% 31.83/4.48      ( ~ v1_partfun1(sK5,X0_53)
% 31.83/4.48      | ~ v4_relat_1(sK5,X0_53)
% 31.83/4.48      | ~ v1_relat_1(sK5)
% 31.83/4.48      | k1_relat_1(sK5) = X0_53 ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_670]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2728,plain,
% 31.83/4.48      ( ~ v1_partfun1(sK5,sK3)
% 31.83/4.48      | ~ v4_relat_1(sK5,sK3)
% 31.83/4.48      | ~ v1_relat_1(sK5)
% 31.83/4.48      | k1_relat_1(sK5) = sK3 ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_2198]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5364,plain,
% 31.83/4.48      ( k1_relat_1(sK5) = sK3 ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_5203,c_35,c_26,c_25,c_24,c_1968,c_2000,c_2384,c_2728]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5368,plain,
% 31.83/4.48      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 31.83/4.48      | r1_xboole_0(X0_53,sK3) != iProver_top
% 31.83/4.48      | v1_relat_1(sK5) != iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5364,c_1535]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_1969,plain,
% 31.83/4.48      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 31.83/4.48      | v1_relat_1(sK5) = iProver_top ),
% 31.83/4.48      inference(predicate_to_equality,[status(thm)],[c_1968]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6207,plain,
% 31.83/4.48      ( r1_xboole_0(X0_53,sK3) != iProver_top
% 31.83/4.48      | k7_relat_1(sK5,X0_53) = k1_xboole_0 ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_5368,c_49,c_1969]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6208,plain,
% 31.83/4.48      ( k7_relat_1(sK5,X0_53) = k1_xboole_0
% 31.83/4.48      | r1_xboole_0(X0_53,sK3) != iProver_top ),
% 31.83/4.48      inference(renaming,[status(thm)],[c_6207]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6215,plain,
% 31.83/4.48      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_3856,c_6208]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2750,plain,
% 31.83/4.48      ( v1_relat_1(sK5) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1550,c_1540]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2926,plain,
% 31.83/4.48      ( k7_relat_1(sK5,k3_xboole_0(X0_53,X1_53)) = k7_relat_1(k7_relat_1(sK5,X0_53),X1_53) ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_2750,c_1534]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6562,plain,
% 31.83/4.48      ( k7_relat_1(sK5,k3_xboole_0(sK2,X0_53)) = k7_relat_1(k1_xboole_0,X0_53) ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_6215,c_2926]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6610,plain,
% 31.83/4.48      ( k7_relat_1(k1_xboole_0,sK3) = k7_relat_1(sK5,k1_xboole_0) ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_3862,c_6562]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_23,negated_conjecture,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 31.83/4.48      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 31.83/4.48      inference(cnf_transformation,[],[f91]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_664,negated_conjecture,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 31.83/4.48      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 31.83/4.48      inference(subtyping,[status(esa)],[c_23]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2416,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 31.83/4.48      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 31.83/4.48      inference(demodulation,[status(thm)],[c_2248,c_664]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_3978,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 31.83/4.48      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 31.83/4.48      inference(demodulation,[status(thm)],[c_3862,c_2416]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5078,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 31.83/4.48      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 31.83/4.48      inference(demodulation,[status(thm)],[c_5074,c_3978]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5691,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 31.83/4.48      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 31.83/4.48      inference(demodulation,[status(thm)],[c_5078,c_5080]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6849,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 31.83/4.48      | k7_relat_1(k1_xboole_0,sK3) != k7_relat_1(sK4,k1_xboole_0) ),
% 31.83/4.48      inference(demodulation,[status(thm)],[c_6610,c_5691]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_5702,plain,
% 31.83/4.48      ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5696,c_1531]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2838,plain,
% 31.83/4.48      ( v4_relat_1(sK5,sK3) = iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_1550,c_1541]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_3618,plain,
% 31.83/4.48      ( k7_relat_1(sK5,sK3) = sK5 | v1_relat_1(sK5) != iProver_top ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_2838,c_1536]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2199,plain,
% 31.83/4.48      ( ~ v4_relat_1(sK5,X0_53)
% 31.83/4.48      | ~ v1_relat_1(sK5)
% 31.83/4.48      | k7_relat_1(sK5,X0_53) = sK5 ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_678]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_2577,plain,
% 31.83/4.48      ( ~ v4_relat_1(sK5,sK3)
% 31.83/4.48      | ~ v1_relat_1(sK5)
% 31.83/4.48      | k7_relat_1(sK5,sK3) = sK5 ),
% 31.83/4.48      inference(instantiation,[status(thm)],[c_2199]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4193,plain,
% 31.83/4.48      ( k7_relat_1(sK5,sK3) = sK5 ),
% 31.83/4.48      inference(global_propositional_subsumption,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_3618,c_24,c_1968,c_2000,c_2577]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_4196,plain,
% 31.83/4.48      ( k7_relat_1(sK5,k3_xboole_0(sK3,X0_53)) = k7_relat_1(sK5,X0_53) ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_4193,c_2926]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_6114,plain,
% 31.83/4.48      ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2) ),
% 31.83/4.48      inference(superposition,[status(thm)],[c_5702,c_4196]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_16095,plain,
% 31.83/4.48      ( k7_relat_1(k1_xboole_0,sK3) = k1_xboole_0 ),
% 31.83/4.48      inference(light_normalisation,[status(thm)],[c_6114,c_6215,c_6610]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_17750,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 31.83/4.48      | k1_xboole_0 != k1_xboole_0 ),
% 31.83/4.48      inference(light_normalisation,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_6849,c_6606,c_16095]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_17751,plain,
% 31.83/4.48      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 31.83/4.48      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 31.83/4.48      inference(equality_resolution_simp,[status(thm)],[c_17750]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_17752,plain,
% 31.83/4.48      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 31.83/4.48      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 31.83/4.48      inference(demodulation,[status(thm)],[c_17751,c_14443]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(c_16098,plain,
% 31.83/4.48      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 31.83/4.48      inference(demodulation,[status(thm)],[c_16095,c_6610]) ).
% 31.83/4.48  
% 31.83/4.48  cnf(contradiction,plain,
% 31.83/4.48      ( $false ),
% 31.83/4.48      inference(minisat,
% 31.83/4.48                [status(thm)],
% 31.83/4.48                [c_70328,c_59470,c_17752,c_16098,c_46,c_45,c_44,c_40,
% 31.83/4.48                 c_39]) ).
% 31.83/4.48  
% 31.83/4.48  
% 31.83/4.48  % SZS output end CNFRefutation for theBenchmark.p
% 31.83/4.48  
% 31.83/4.48  ------                               Statistics
% 31.83/4.48  
% 31.83/4.48  ------ Selected
% 31.83/4.48  
% 31.83/4.48  total_time:                             3.993
% 31.83/4.48  
%------------------------------------------------------------------------------
