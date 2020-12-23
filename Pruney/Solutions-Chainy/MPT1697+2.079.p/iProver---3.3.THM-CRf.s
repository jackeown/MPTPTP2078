%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:40 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  190 (1551 expanded)
%              Number of clauses        :  109 ( 360 expanded)
%              Number of leaves         :   22 ( 600 expanded)
%              Depth                    :   20
%              Number of atoms          : 1025 (18213 expanded)
%              Number of equality atoms :  370 (4352 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f81])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f32,plain,(
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
    inference(flattening,[],[f32])).

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f44,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f43,f42,f41,f40,f39,f38])).

fof(f73,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f82])).

fof(f79,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f77,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

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

fof(f28,plain,(
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
    inference(flattening,[],[f28])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,(
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
    inference(equality_resolution,[],[f61])).

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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

fof(f64,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f80,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_233,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_26,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_417,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_418,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_420,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_418,c_30,c_28])).

cnf(c_431,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_420])).

cnf(c_432,plain,
    ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1134,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k2_enumset1(X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1151,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2373,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,sK3)) = k9_subset_1(sK0,X0,sK3) ),
    inference(superposition,[status(thm)],[c_1134,c_1151])).

cnf(c_2674,plain,
    ( k9_subset_1(sK0,sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_432,c_2373])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1140,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1145,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2530,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_1145])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1601,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1755,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_1601])).

cnf(c_3254,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2530,c_22,c_20,c_1755])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1137,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2531,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_1145])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1606,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1812,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_1606])).

cnf(c_3486,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2531,c_25,c_23,c_1812])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f89])).

cnf(c_18,plain,
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
    inference(cnf_transformation,[],[f64])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f65])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f66])).

cnf(c_170,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_18,c_17,c_16])).

cnf(c_171,plain,
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
    inference(renaming,[status(thm)],[c_170])).

cnf(c_1128,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1150,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1348,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
    | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X0) = X2
    | v1_funct_2(X5,X4,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1128,c_1150])).

cnf(c_9448,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3486,c_1348])).

cnf(c_31,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_35,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_41,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_42,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_11649,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9448,c_34,c_35,c_40,c_41,c_42])).

cnf(c_11650,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_11649])).

cnf(c_11663,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3254,c_11650])).

cnf(c_37,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_43,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_44,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_45,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12154,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11663,c_37,c_43,c_44,c_45])).

cnf(c_12164,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2674,c_12154])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1149,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2248,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1140,c_1149])).

cnf(c_1798,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1))
    | v1_relat_1(sK5) ),
    inference(resolution,[status(thm)],[c_6,c_20])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1986,plain,
    ( v1_relat_1(sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1798,c_9])).

cnf(c_1987,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1986])).

cnf(c_2764,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2248,c_1987])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1153,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1147,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1152,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2053,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1152])).

cnf(c_2141,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_2053])).

cnf(c_2769,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2764,c_2141])).

cnf(c_2249,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1137,c_1149])).

cnf(c_1800,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_6,c_23])).

cnf(c_1993,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1800,c_9])).

cnf(c_1994,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1993])).

cnf(c_2893,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2249,c_1994])).

cnf(c_2898,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2893,c_2141])).

cnf(c_12165,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12164,c_2674,c_2769,c_2898])).

cnf(c_12166,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12165])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f88])).

cnf(c_177,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_18,c_17,c_16])).

cnf(c_178,plain,
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
    inference(renaming,[status(thm)],[c_177])).

cnf(c_1127,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_178])).

cnf(c_1320,plain,
    ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
    | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X4) = X5
    | v1_funct_2(X5,X4,X1) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1127,c_1150])).

cnf(c_7358,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3486,c_1320])).

cnf(c_9025,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7358,c_34,c_35,c_40,c_41,c_42])).

cnf(c_9026,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_9025])).

cnf(c_9039,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3254,c_9026])).

cnf(c_10091,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9039,c_37,c_43,c_44,c_45])).

cnf(c_10101,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2674,c_10091])).

cnf(c_10102,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10101,c_2674,c_2769,c_2898])).

cnf(c_10103,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10102])).

cnf(c_19,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3258,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_3254,c_19])).

cnf(c_3490,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_3486,c_3258])).

cnf(c_3786,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2674,c_3490])).

cnf(c_3787,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3786,c_2769,c_2898])).

cnf(c_3788,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_3787])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12166,c_10103,c_3788,c_38,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.08  % Command    : iproveropt_run.sh %d %s
% 0.07/0.26  % Computer   : n016.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 13:22:19 EST 2020
% 0.11/0.27  % CPUTime    : 
% 0.11/0.27  % Running in FOF mode
% 4.04/0.87  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.04/0.87  
% 4.04/0.87  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/0.87  
% 4.04/0.87  ------  iProver source info
% 4.04/0.87  
% 4.04/0.87  git: date: 2020-06-30 10:37:57 +0100
% 4.04/0.87  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/0.87  git: non_committed_changes: false
% 4.04/0.87  git: last_make_outside_of_git: false
% 4.04/0.87  
% 4.04/0.87  ------ 
% 4.04/0.87  ------ Parsing...
% 4.04/0.87  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/0.87  
% 4.04/0.87  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.04/0.87  
% 4.04/0.87  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/0.87  
% 4.04/0.87  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/0.87  ------ Proving...
% 4.04/0.87  ------ Problem Properties 
% 4.04/0.87  
% 4.04/0.87  
% 4.04/0.87  clauses                                 29
% 4.04/0.87  conjectures                             13
% 4.04/0.87  EPR                                     10
% 4.04/0.87  Horn                                    23
% 4.04/0.87  unary                                   15
% 4.04/0.87  binary                                  2
% 4.04/0.87  lits                                    121
% 4.04/0.87  lits eq                                 13
% 4.04/0.87  fd_pure                                 0
% 4.04/0.87  fd_pseudo                               0
% 4.04/0.87  fd_cond                                 1
% 4.04/0.87  fd_pseudo_cond                          0
% 4.04/0.87  AC symbols                              0
% 4.04/0.87  
% 4.04/0.87  ------ Input Options Time Limit: Unbounded
% 4.04/0.87  
% 4.04/0.87  
% 4.04/0.87  ------ 
% 4.04/0.87  Current options:
% 4.04/0.87  ------ 
% 4.04/0.87  
% 4.04/0.87  
% 4.04/0.87  
% 4.04/0.87  
% 4.04/0.87  ------ Proving...
% 4.04/0.87  
% 4.04/0.87  
% 4.04/0.87  % SZS status Theorem for theBenchmark.p
% 4.04/0.87  
% 4.04/0.87  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/0.87  
% 4.04/0.87  fof(f1,axiom,(
% 4.04/0.87    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f34,plain,(
% 4.04/0.87    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.04/0.87    inference(nnf_transformation,[],[f1])).
% 4.04/0.87  
% 4.04/0.87  fof(f45,plain,(
% 4.04/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f34])).
% 4.04/0.87  
% 4.04/0.87  fof(f8,axiom,(
% 4.04/0.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f53,plain,(
% 4.04/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.04/0.87    inference(cnf_transformation,[],[f8])).
% 4.04/0.87  
% 4.04/0.87  fof(f4,axiom,(
% 4.04/0.87    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f49,plain,(
% 4.04/0.87    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f4])).
% 4.04/0.87  
% 4.04/0.87  fof(f5,axiom,(
% 4.04/0.87    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f50,plain,(
% 4.04/0.87    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f5])).
% 4.04/0.87  
% 4.04/0.87  fof(f81,plain,(
% 4.04/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 4.04/0.87    inference(definition_unfolding,[],[f49,f50])).
% 4.04/0.87  
% 4.04/0.87  fof(f82,plain,(
% 4.04/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 4.04/0.87    inference(definition_unfolding,[],[f53,f81])).
% 4.04/0.87  
% 4.04/0.87  fof(f84,plain,(
% 4.04/0.87    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.04/0.87    inference(definition_unfolding,[],[f45,f82])).
% 4.04/0.87  
% 4.04/0.87  fof(f12,axiom,(
% 4.04/0.87    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f24,plain,(
% 4.04/0.87    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 4.04/0.87    inference(ennf_transformation,[],[f12])).
% 4.04/0.87  
% 4.04/0.87  fof(f25,plain,(
% 4.04/0.87    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 4.04/0.87    inference(flattening,[],[f24])).
% 4.04/0.87  
% 4.04/0.87  fof(f35,plain,(
% 4.04/0.87    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 4.04/0.87    inference(nnf_transformation,[],[f25])).
% 4.04/0.87  
% 4.04/0.87  fof(f58,plain,(
% 4.04/0.87    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f35])).
% 4.04/0.87  
% 4.04/0.87  fof(f16,conjecture,(
% 4.04/0.87    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f17,negated_conjecture,(
% 4.04/0.87    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 4.04/0.87    inference(negated_conjecture,[],[f16])).
% 4.04/0.87  
% 4.04/0.87  fof(f32,plain,(
% 4.04/0.87    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 4.04/0.87    inference(ennf_transformation,[],[f17])).
% 4.04/0.87  
% 4.04/0.87  fof(f33,plain,(
% 4.04/0.87    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 4.04/0.87    inference(flattening,[],[f32])).
% 4.04/0.87  
% 4.04/0.87  fof(f43,plain,(
% 4.04/0.87    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 4.04/0.87    introduced(choice_axiom,[])).
% 4.04/0.87  
% 4.04/0.87  fof(f42,plain,(
% 4.04/0.87    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 4.04/0.87    introduced(choice_axiom,[])).
% 4.04/0.87  
% 4.04/0.87  fof(f41,plain,(
% 4.04/0.87    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 4.04/0.87    introduced(choice_axiom,[])).
% 4.04/0.87  
% 4.04/0.87  fof(f40,plain,(
% 4.04/0.87    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 4.04/0.87    introduced(choice_axiom,[])).
% 4.04/0.87  
% 4.04/0.87  fof(f39,plain,(
% 4.04/0.87    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 4.04/0.87    introduced(choice_axiom,[])).
% 4.04/0.87  
% 4.04/0.87  fof(f38,plain,(
% 4.04/0.87    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 4.04/0.87    introduced(choice_axiom,[])).
% 4.04/0.87  
% 4.04/0.87  fof(f44,plain,(
% 4.04/0.87    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 4.04/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f43,f42,f41,f40,f39,f38])).
% 4.04/0.87  
% 4.04/0.87  fof(f73,plain,(
% 4.04/0.87    r1_subset_1(sK2,sK3)),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f69,plain,(
% 4.04/0.87    ~v1_xboole_0(sK2)),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f71,plain,(
% 4.04/0.87    ~v1_xboole_0(sK3)),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f72,plain,(
% 4.04/0.87    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f6,axiom,(
% 4.04/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f19,plain,(
% 4.04/0.87    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.04/0.87    inference(ennf_transformation,[],[f6])).
% 4.04/0.87  
% 4.04/0.87  fof(f51,plain,(
% 4.04/0.87    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.04/0.87    inference(cnf_transformation,[],[f19])).
% 4.04/0.87  
% 4.04/0.87  fof(f85,plain,(
% 4.04/0.87    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.04/0.87    inference(definition_unfolding,[],[f51,f82])).
% 4.04/0.87  
% 4.04/0.87  fof(f79,plain,(
% 4.04/0.87    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f13,axiom,(
% 4.04/0.87    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f26,plain,(
% 4.04/0.87    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.04/0.87    inference(ennf_transformation,[],[f13])).
% 4.04/0.87  
% 4.04/0.87  fof(f27,plain,(
% 4.04/0.87    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.04/0.87    inference(flattening,[],[f26])).
% 4.04/0.87  
% 4.04/0.87  fof(f60,plain,(
% 4.04/0.87    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f27])).
% 4.04/0.87  
% 4.04/0.87  fof(f77,plain,(
% 4.04/0.87    v1_funct_1(sK5)),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f76,plain,(
% 4.04/0.87    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f74,plain,(
% 4.04/0.87    v1_funct_1(sK4)),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f14,axiom,(
% 4.04/0.87    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f28,plain,(
% 4.04/0.87    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.04/0.87    inference(ennf_transformation,[],[f14])).
% 4.04/0.87  
% 4.04/0.87  fof(f29,plain,(
% 4.04/0.87    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.04/0.87    inference(flattening,[],[f28])).
% 4.04/0.87  
% 4.04/0.87  fof(f36,plain,(
% 4.04/0.87    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.04/0.87    inference(nnf_transformation,[],[f29])).
% 4.04/0.87  
% 4.04/0.87  fof(f37,plain,(
% 4.04/0.87    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.04/0.87    inference(flattening,[],[f36])).
% 4.04/0.87  
% 4.04/0.87  fof(f61,plain,(
% 4.04/0.87    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f37])).
% 4.04/0.87  
% 4.04/0.87  fof(f89,plain,(
% 4.04/0.87    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/0.87    inference(equality_resolution,[],[f61])).
% 4.04/0.87  
% 4.04/0.87  fof(f15,axiom,(
% 4.04/0.87    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f30,plain,(
% 4.04/0.87    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 4.04/0.87    inference(ennf_transformation,[],[f15])).
% 4.04/0.87  
% 4.04/0.87  fof(f31,plain,(
% 4.04/0.87    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 4.04/0.87    inference(flattening,[],[f30])).
% 4.04/0.87  
% 4.04/0.87  fof(f64,plain,(
% 4.04/0.87    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f31])).
% 4.04/0.87  
% 4.04/0.87  fof(f65,plain,(
% 4.04/0.87    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f31])).
% 4.04/0.87  
% 4.04/0.87  fof(f66,plain,(
% 4.04/0.87    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f31])).
% 4.04/0.87  
% 4.04/0.87  fof(f7,axiom,(
% 4.04/0.87    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f20,plain,(
% 4.04/0.87    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 4.04/0.87    inference(ennf_transformation,[],[f7])).
% 4.04/0.87  
% 4.04/0.87  fof(f52,plain,(
% 4.04/0.87    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f20])).
% 4.04/0.87  
% 4.04/0.87  fof(f68,plain,(
% 4.04/0.87    ~v1_xboole_0(sK1)),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f75,plain,(
% 4.04/0.87    v1_funct_2(sK4,sK2,sK1)),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f78,plain,(
% 4.04/0.87    v1_funct_2(sK5,sK3,sK1)),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f9,axiom,(
% 4.04/0.87    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f21,plain,(
% 4.04/0.87    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 4.04/0.87    inference(ennf_transformation,[],[f9])).
% 4.04/0.87  
% 4.04/0.87  fof(f54,plain,(
% 4.04/0.87    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f21])).
% 4.04/0.87  
% 4.04/0.87  fof(f11,axiom,(
% 4.04/0.87    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f57,plain,(
% 4.04/0.87    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 4.04/0.87    inference(cnf_transformation,[],[f11])).
% 4.04/0.87  
% 4.04/0.87  fof(f2,axiom,(
% 4.04/0.87    v1_xboole_0(k1_xboole_0)),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f47,plain,(
% 4.04/0.87    v1_xboole_0(k1_xboole_0)),
% 4.04/0.87    inference(cnf_transformation,[],[f2])).
% 4.04/0.87  
% 4.04/0.87  fof(f10,axiom,(
% 4.04/0.87    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f22,plain,(
% 4.04/0.87    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 4.04/0.87    inference(ennf_transformation,[],[f10])).
% 4.04/0.87  
% 4.04/0.87  fof(f23,plain,(
% 4.04/0.87    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 4.04/0.87    inference(flattening,[],[f22])).
% 4.04/0.87  
% 4.04/0.87  fof(f55,plain,(
% 4.04/0.87    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f23])).
% 4.04/0.87  
% 4.04/0.87  fof(f3,axiom,(
% 4.04/0.87    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 4.04/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.04/0.87  
% 4.04/0.87  fof(f18,plain,(
% 4.04/0.87    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 4.04/0.87    inference(ennf_transformation,[],[f3])).
% 4.04/0.87  
% 4.04/0.87  fof(f48,plain,(
% 4.04/0.87    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f18])).
% 4.04/0.87  
% 4.04/0.87  fof(f62,plain,(
% 4.04/0.87    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/0.87    inference(cnf_transformation,[],[f37])).
% 4.04/0.87  
% 4.04/0.87  fof(f88,plain,(
% 4.04/0.87    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/0.87    inference(equality_resolution,[],[f62])).
% 4.04/0.87  
% 4.04/0.87  fof(f80,plain,(
% 4.04/0.87    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  fof(f70,plain,(
% 4.04/0.87    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 4.04/0.87    inference(cnf_transformation,[],[f44])).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1,plain,
% 4.04/0.87      ( ~ r1_xboole_0(X0,X1)
% 4.04/0.87      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
% 4.04/0.87      inference(cnf_transformation,[],[f84]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_233,plain,
% 4.04/0.87      ( ~ r1_xboole_0(X0,X1)
% 4.04/0.87      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
% 4.04/0.87      inference(prop_impl,[status(thm)],[c_1]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_11,plain,
% 4.04/0.87      ( ~ r1_subset_1(X0,X1)
% 4.04/0.87      | r1_xboole_0(X0,X1)
% 4.04/0.87      | v1_xboole_0(X0)
% 4.04/0.87      | v1_xboole_0(X1) ),
% 4.04/0.87      inference(cnf_transformation,[],[f58]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_26,negated_conjecture,
% 4.04/0.87      ( r1_subset_1(sK2,sK3) ),
% 4.04/0.87      inference(cnf_transformation,[],[f73]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_417,plain,
% 4.04/0.87      ( r1_xboole_0(X0,X1)
% 4.04/0.87      | v1_xboole_0(X0)
% 4.04/0.87      | v1_xboole_0(X1)
% 4.04/0.87      | sK3 != X1
% 4.04/0.87      | sK2 != X0 ),
% 4.04/0.87      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_418,plain,
% 4.04/0.87      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 4.04/0.87      inference(unflattening,[status(thm)],[c_417]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_30,negated_conjecture,
% 4.04/0.87      ( ~ v1_xboole_0(sK2) ),
% 4.04/0.87      inference(cnf_transformation,[],[f69]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_28,negated_conjecture,
% 4.04/0.87      ( ~ v1_xboole_0(sK3) ),
% 4.04/0.87      inference(cnf_transformation,[],[f71]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_420,plain,
% 4.04/0.87      ( r1_xboole_0(sK2,sK3) ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_418,c_30,c_28]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_431,plain,
% 4.04/0.87      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0
% 4.04/0.87      | sK3 != X1
% 4.04/0.87      | sK2 != X0 ),
% 4.04/0.87      inference(resolution_lifted,[status(thm)],[c_233,c_420]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_432,plain,
% 4.04/0.87      ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)) = k1_xboole_0 ),
% 4.04/0.87      inference(unflattening,[status(thm)],[c_431]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_27,negated_conjecture,
% 4.04/0.87      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 4.04/0.87      inference(cnf_transformation,[],[f72]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1134,plain,
% 4.04/0.87      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_4,plain,
% 4.04/0.87      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/0.87      | k1_setfam_1(k2_enumset1(X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 4.04/0.87      inference(cnf_transformation,[],[f85]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1151,plain,
% 4.04/0.87      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 4.04/0.87      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2373,plain,
% 4.04/0.87      ( k1_setfam_1(k2_enumset1(X0,X0,X0,sK3)) = k9_subset_1(sK0,X0,sK3) ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_1134,c_1151]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2674,plain,
% 4.04/0.87      ( k9_subset_1(sK0,sK2,sK3) = k1_xboole_0 ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_432,c_2373]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_20,negated_conjecture,
% 4.04/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 4.04/0.87      inference(cnf_transformation,[],[f79]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1140,plain,
% 4.04/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_12,plain,
% 4.04/0.87      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/0.87      | ~ v1_funct_1(X0)
% 4.04/0.87      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 4.04/0.87      inference(cnf_transformation,[],[f60]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1145,plain,
% 4.04/0.87      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 4.04/0.87      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/0.87      | v1_funct_1(X2) != iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2530,plain,
% 4.04/0.87      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
% 4.04/0.87      | v1_funct_1(sK5) != iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_1140,c_1145]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_22,negated_conjecture,
% 4.04/0.87      ( v1_funct_1(sK5) ),
% 4.04/0.87      inference(cnf_transformation,[],[f77]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1601,plain,
% 4.04/0.87      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.04/0.87      | ~ v1_funct_1(sK5)
% 4.04/0.87      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 4.04/0.87      inference(instantiation,[status(thm)],[c_12]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1755,plain,
% 4.04/0.87      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 4.04/0.87      | ~ v1_funct_1(sK5)
% 4.04/0.87      | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 4.04/0.87      inference(instantiation,[status(thm)],[c_1601]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_3254,plain,
% 4.04/0.87      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_2530,c_22,c_20,c_1755]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_23,negated_conjecture,
% 4.04/0.87      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 4.04/0.87      inference(cnf_transformation,[],[f76]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1137,plain,
% 4.04/0.87      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2531,plain,
% 4.04/0.87      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
% 4.04/0.87      | v1_funct_1(sK4) != iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_1137,c_1145]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_25,negated_conjecture,
% 4.04/0.87      ( v1_funct_1(sK4) ),
% 4.04/0.87      inference(cnf_transformation,[],[f74]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1606,plain,
% 4.04/0.87      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.04/0.87      | ~ v1_funct_1(sK4)
% 4.04/0.87      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 4.04/0.87      inference(instantiation,[status(thm)],[c_12]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1812,plain,
% 4.04/0.87      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 4.04/0.87      | ~ v1_funct_1(sK4)
% 4.04/0.87      | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 4.04/0.87      inference(instantiation,[status(thm)],[c_1606]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_3486,plain,
% 4.04/0.87      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_2531,c_25,c_23,c_1812]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_15,plain,
% 4.04/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/0.87      | ~ v1_funct_2(X3,X4,X2)
% 4.04/0.87      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 4.04/0.87      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/0.87      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/0.87      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 4.04/0.87      | ~ v1_funct_1(X0)
% 4.04/0.87      | ~ v1_funct_1(X3)
% 4.04/0.87      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 4.04/0.87      | v1_xboole_0(X5)
% 4.04/0.87      | v1_xboole_0(X2)
% 4.04/0.87      | v1_xboole_0(X4)
% 4.04/0.87      | v1_xboole_0(X1)
% 4.04/0.87      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 4.04/0.87      inference(cnf_transformation,[],[f89]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_18,plain,
% 4.04/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/0.87      | ~ v1_funct_2(X3,X4,X2)
% 4.04/0.87      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/0.87      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/0.87      | ~ v1_funct_1(X0)
% 4.04/0.87      | ~ v1_funct_1(X3)
% 4.04/0.87      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 4.04/0.87      | v1_xboole_0(X5)
% 4.04/0.87      | v1_xboole_0(X2)
% 4.04/0.87      | v1_xboole_0(X4)
% 4.04/0.87      | v1_xboole_0(X1) ),
% 4.04/0.87      inference(cnf_transformation,[],[f64]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_17,plain,
% 4.04/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/0.87      | ~ v1_funct_2(X3,X4,X2)
% 4.04/0.87      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 4.04/0.87      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/0.87      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/0.87      | ~ v1_funct_1(X0)
% 4.04/0.87      | ~ v1_funct_1(X3)
% 4.04/0.87      | v1_xboole_0(X5)
% 4.04/0.87      | v1_xboole_0(X2)
% 4.04/0.87      | v1_xboole_0(X4)
% 4.04/0.87      | v1_xboole_0(X1) ),
% 4.04/0.87      inference(cnf_transformation,[],[f65]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_16,plain,
% 4.04/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/0.87      | ~ v1_funct_2(X3,X4,X2)
% 4.04/0.87      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/0.87      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/0.87      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 4.04/0.87      | ~ v1_funct_1(X0)
% 4.04/0.87      | ~ v1_funct_1(X3)
% 4.04/0.87      | v1_xboole_0(X5)
% 4.04/0.87      | v1_xboole_0(X2)
% 4.04/0.87      | v1_xboole_0(X4)
% 4.04/0.87      | v1_xboole_0(X1) ),
% 4.04/0.87      inference(cnf_transformation,[],[f66]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_170,plain,
% 4.04/0.87      ( ~ v1_funct_1(X3)
% 4.04/0.87      | ~ v1_funct_1(X0)
% 4.04/0.87      | ~ v1_funct_2(X3,X4,X2)
% 4.04/0.87      | ~ v1_funct_2(X0,X1,X2)
% 4.04/0.87      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/0.87      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/0.87      | v1_xboole_0(X5)
% 4.04/0.87      | v1_xboole_0(X2)
% 4.04/0.87      | v1_xboole_0(X4)
% 4.04/0.87      | v1_xboole_0(X1)
% 4.04/0.87      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_15,c_18,c_17,c_16]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_171,plain,
% 4.04/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/0.87      | ~ v1_funct_2(X3,X4,X2)
% 4.04/0.87      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/0.87      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/0.87      | ~ v1_funct_1(X0)
% 4.04/0.87      | ~ v1_funct_1(X3)
% 4.04/0.87      | v1_xboole_0(X1)
% 4.04/0.87      | v1_xboole_0(X2)
% 4.04/0.87      | v1_xboole_0(X4)
% 4.04/0.87      | v1_xboole_0(X5)
% 4.04/0.87      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 4.04/0.87      inference(renaming,[status(thm)],[c_170]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1128,plain,
% 4.04/0.87      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 4.04/0.87      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.04/0.87      | v1_funct_2(X5,X4,X1) != iProver_top
% 4.04/0.87      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 4.04/0.87      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 4.04/0.87      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/0.87      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 4.04/0.87      | v1_funct_1(X2) != iProver_top
% 4.04/0.87      | v1_funct_1(X5) != iProver_top
% 4.04/0.87      | v1_xboole_0(X3) = iProver_top
% 4.04/0.87      | v1_xboole_0(X1) = iProver_top
% 4.04/0.87      | v1_xboole_0(X4) = iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_171]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_5,plain,
% 4.04/0.87      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/0.87      | ~ v1_xboole_0(X1)
% 4.04/0.87      | v1_xboole_0(X0) ),
% 4.04/0.87      inference(cnf_transformation,[],[f52]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1150,plain,
% 4.04/0.87      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.04/0.87      | v1_xboole_0(X1) != iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1348,plain,
% 4.04/0.87      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X0) = X2
% 4.04/0.87      | v1_funct_2(X5,X4,X1) != iProver_top
% 4.04/0.87      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.04/0.87      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 4.04/0.87      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 4.04/0.87      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 4.04/0.87      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/0.87      | v1_funct_1(X5) != iProver_top
% 4.04/0.87      | v1_funct_1(X2) != iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top
% 4.04/0.87      | v1_xboole_0(X1) = iProver_top
% 4.04/0.87      | v1_xboole_0(X4) = iProver_top ),
% 4.04/0.87      inference(forward_subsumption_resolution,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_1128,c_1150]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_9448,plain,
% 4.04/0.87      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
% 4.04/0.87      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/0.87      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 4.04/0.87      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/0.87      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | v1_funct_1(X1) != iProver_top
% 4.04/0.87      | v1_funct_1(sK4) != iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top
% 4.04/0.87      | v1_xboole_0(sK1) = iProver_top
% 4.04/0.87      | v1_xboole_0(sK2) = iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_3486,c_1348]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_31,negated_conjecture,
% 4.04/0.87      ( ~ v1_xboole_0(sK1) ),
% 4.04/0.87      inference(cnf_transformation,[],[f68]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_34,plain,
% 4.04/0.87      ( v1_xboole_0(sK1) != iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_35,plain,
% 4.04/0.87      ( v1_xboole_0(sK2) != iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_40,plain,
% 4.04/0.87      ( v1_funct_1(sK4) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_24,negated_conjecture,
% 4.04/0.87      ( v1_funct_2(sK4,sK2,sK1) ),
% 4.04/0.87      inference(cnf_transformation,[],[f75]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_41,plain,
% 4.04/0.87      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_42,plain,
% 4.04/0.87      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_11649,plain,
% 4.04/0.87      ( v1_funct_1(X1) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/0.87      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
% 4.04/0.87      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/0.87      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_9448,c_34,c_35,c_40,c_41,c_42]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_11650,plain,
% 4.04/0.87      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
% 4.04/0.87      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/0.87      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | v1_funct_1(X1) != iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.87      inference(renaming,[status(thm)],[c_11649]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_11663,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 4.04/0.87      | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
% 4.04/0.87      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 4.04/0.87      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 4.04/0.87      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 4.04/0.87      | v1_funct_1(sK5) != iProver_top
% 4.04/0.87      | v1_xboole_0(sK3) = iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_3254,c_11650]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_37,plain,
% 4.04/0.87      ( v1_xboole_0(sK3) != iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_43,plain,
% 4.04/0.87      ( v1_funct_1(sK5) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_21,negated_conjecture,
% 4.04/0.87      ( v1_funct_2(sK5,sK3,sK1) ),
% 4.04/0.87      inference(cnf_transformation,[],[f78]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_44,plain,
% 4.04/0.87      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_45,plain,
% 4.04/0.87      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_12154,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 4.04/0.87      | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
% 4.04/0.87      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_11663,c_37,c_43,c_44,c_45]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_12164,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 4.04/0.87      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 4.04/0.87      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_2674,c_12154]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_6,plain,
% 4.04/0.87      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/0.87      | ~ v1_relat_1(X1)
% 4.04/0.87      | v1_relat_1(X0) ),
% 4.04/0.87      inference(cnf_transformation,[],[f54]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1149,plain,
% 4.04/0.87      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.04/0.87      | v1_relat_1(X1) != iProver_top
% 4.04/0.87      | v1_relat_1(X0) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2248,plain,
% 4.04/0.87      ( v1_relat_1(k2_zfmisc_1(sK3,sK1)) != iProver_top
% 4.04/0.87      | v1_relat_1(sK5) = iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_1140,c_1149]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1798,plain,
% 4.04/0.87      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK1)) | v1_relat_1(sK5) ),
% 4.04/0.87      inference(resolution,[status(thm)],[c_6,c_20]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_9,plain,
% 4.04/0.87      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 4.04/0.87      inference(cnf_transformation,[],[f57]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1986,plain,
% 4.04/0.87      ( v1_relat_1(sK5) ),
% 4.04/0.87      inference(forward_subsumption_resolution,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_1798,c_9]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1987,plain,
% 4.04/0.87      ( v1_relat_1(sK5) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_1986]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2764,plain,
% 4.04/0.87      ( v1_relat_1(sK5) = iProver_top ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_2248,c_1987]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2,plain,
% 4.04/0.87      ( v1_xboole_0(k1_xboole_0) ),
% 4.04/0.87      inference(cnf_transformation,[],[f47]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1153,plain,
% 4.04/0.87      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_8,plain,
% 4.04/0.87      ( ~ v1_relat_1(X0)
% 4.04/0.87      | ~ v1_xboole_0(X1)
% 4.04/0.87      | v1_xboole_0(k7_relat_1(X0,X1)) ),
% 4.04/0.87      inference(cnf_transformation,[],[f55]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1147,plain,
% 4.04/0.87      ( v1_relat_1(X0) != iProver_top
% 4.04/0.87      | v1_xboole_0(X1) != iProver_top
% 4.04/0.87      | v1_xboole_0(k7_relat_1(X0,X1)) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_3,plain,
% 4.04/0.87      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 4.04/0.87      inference(cnf_transformation,[],[f48]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1152,plain,
% 4.04/0.87      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2053,plain,
% 4.04/0.87      ( k7_relat_1(X0,X1) = k1_xboole_0
% 4.04/0.87      | v1_relat_1(X0) != iProver_top
% 4.04/0.87      | v1_xboole_0(X1) != iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_1147,c_1152]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2141,plain,
% 4.04/0.87      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 4.04/0.87      | v1_relat_1(X0) != iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_1153,c_2053]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2769,plain,
% 4.04/0.87      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_2764,c_2141]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2249,plain,
% 4.04/0.87      ( v1_relat_1(k2_zfmisc_1(sK2,sK1)) != iProver_top
% 4.04/0.87      | v1_relat_1(sK4) = iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_1137,c_1149]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1800,plain,
% 4.04/0.87      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1)) | v1_relat_1(sK4) ),
% 4.04/0.87      inference(resolution,[status(thm)],[c_6,c_23]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1993,plain,
% 4.04/0.87      ( v1_relat_1(sK4) ),
% 4.04/0.87      inference(forward_subsumption_resolution,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_1800,c_9]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1994,plain,
% 4.04/0.87      ( v1_relat_1(sK4) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_1993]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2893,plain,
% 4.04/0.87      ( v1_relat_1(sK4) = iProver_top ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_2249,c_1994]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_2898,plain,
% 4.04/0.87      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_2893,c_2141]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_12165,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 4.04/0.87      | k1_xboole_0 != k1_xboole_0
% 4.04/0.87      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/0.87      inference(light_normalisation,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_12164,c_2674,c_2769,c_2898]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_12166,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 4.04/0.87      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/0.87      inference(equality_resolution_simp,[status(thm)],[c_12165]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_14,plain,
% 4.04/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/0.87      | ~ v1_funct_2(X3,X4,X2)
% 4.04/0.87      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 4.04/0.87      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/0.87      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/0.87      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 4.04/0.87      | ~ v1_funct_1(X0)
% 4.04/0.87      | ~ v1_funct_1(X3)
% 4.04/0.87      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 4.04/0.87      | v1_xboole_0(X5)
% 4.04/0.87      | v1_xboole_0(X2)
% 4.04/0.87      | v1_xboole_0(X4)
% 4.04/0.87      | v1_xboole_0(X1)
% 4.04/0.87      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 4.04/0.87      inference(cnf_transformation,[],[f88]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_177,plain,
% 4.04/0.87      ( ~ v1_funct_1(X3)
% 4.04/0.87      | ~ v1_funct_1(X0)
% 4.04/0.87      | ~ v1_funct_2(X3,X4,X2)
% 4.04/0.87      | ~ v1_funct_2(X0,X1,X2)
% 4.04/0.87      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/0.87      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/0.87      | v1_xboole_0(X5)
% 4.04/0.87      | v1_xboole_0(X2)
% 4.04/0.87      | v1_xboole_0(X4)
% 4.04/0.87      | v1_xboole_0(X1)
% 4.04/0.87      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_14,c_18,c_17,c_16]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_178,plain,
% 4.04/0.87      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/0.87      | ~ v1_funct_2(X3,X4,X2)
% 4.04/0.87      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/0.87      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/0.87      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/0.87      | ~ v1_funct_1(X0)
% 4.04/0.87      | ~ v1_funct_1(X3)
% 4.04/0.87      | v1_xboole_0(X1)
% 4.04/0.87      | v1_xboole_0(X2)
% 4.04/0.87      | v1_xboole_0(X4)
% 4.04/0.87      | v1_xboole_0(X5)
% 4.04/0.87      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 4.04/0.87      inference(renaming,[status(thm)],[c_177]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1127,plain,
% 4.04/0.87      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 4.04/0.87      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.04/0.87      | v1_funct_2(X5,X4,X1) != iProver_top
% 4.04/0.87      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 4.04/0.87      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 4.04/0.87      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/0.87      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 4.04/0.87      | v1_funct_1(X2) != iProver_top
% 4.04/0.87      | v1_funct_1(X5) != iProver_top
% 4.04/0.87      | v1_xboole_0(X3) = iProver_top
% 4.04/0.87      | v1_xboole_0(X1) = iProver_top
% 4.04/0.87      | v1_xboole_0(X4) = iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_178]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_1320,plain,
% 4.04/0.87      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X4) = X5
% 4.04/0.87      | v1_funct_2(X5,X4,X1) != iProver_top
% 4.04/0.87      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.04/0.87      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 4.04/0.87      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 4.04/0.87      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 4.04/0.87      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/0.87      | v1_funct_1(X5) != iProver_top
% 4.04/0.87      | v1_funct_1(X2) != iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top
% 4.04/0.87      | v1_xboole_0(X1) = iProver_top
% 4.04/0.87      | v1_xboole_0(X4) = iProver_top ),
% 4.04/0.87      inference(forward_subsumption_resolution,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_1127,c_1150]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_7358,plain,
% 4.04/0.87      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 4.04/0.87      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/0.87      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 4.04/0.87      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/0.87      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | v1_funct_1(X1) != iProver_top
% 4.04/0.87      | v1_funct_1(sK4) != iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top
% 4.04/0.87      | v1_xboole_0(sK1) = iProver_top
% 4.04/0.87      | v1_xboole_0(sK2) = iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_3486,c_1320]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_9025,plain,
% 4.04/0.87      ( v1_funct_1(X1) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/0.87      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 4.04/0.87      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/0.87      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_7358,c_34,c_35,c_40,c_41,c_42]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_9026,plain,
% 4.04/0.87      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/0.87      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 4.04/0.87      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/0.87      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/0.87      | v1_funct_1(X1) != iProver_top
% 4.04/0.87      | v1_xboole_0(X0) = iProver_top ),
% 4.04/0.87      inference(renaming,[status(thm)],[c_9025]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_9039,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 4.04/0.87      | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
% 4.04/0.87      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 4.04/0.87      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 4.04/0.87      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 4.04/0.87      | v1_funct_1(sK5) != iProver_top
% 4.04/0.87      | v1_xboole_0(sK3) = iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_3254,c_9026]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_10091,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 4.04/0.87      | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
% 4.04/0.87      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 4.04/0.87      inference(global_propositional_subsumption,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_9039,c_37,c_43,c_44,c_45]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_10101,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 4.04/0.87      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 4.04/0.87      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/0.87      inference(superposition,[status(thm)],[c_2674,c_10091]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_10102,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 4.04/0.87      | k1_xboole_0 != k1_xboole_0
% 4.04/0.87      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/0.87      inference(light_normalisation,
% 4.04/0.87                [status(thm)],
% 4.04/0.87                [c_10101,c_2674,c_2769,c_2898]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_10103,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 4.04/0.87      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/0.87      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/0.87      inference(equality_resolution_simp,[status(thm)],[c_10102]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_19,negated_conjecture,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/0.87      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 4.04/0.87      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 4.04/0.87      inference(cnf_transformation,[],[f80]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_3258,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/0.87      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 4.04/0.87      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 4.04/0.87      inference(demodulation,[status(thm)],[c_3254,c_19]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_3490,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/0.87      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 4.04/0.87      | k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 4.04/0.87      inference(demodulation,[status(thm)],[c_3486,c_3258]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_3786,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/0.87      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 4.04/0.87      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 4.04/0.87      inference(demodulation,[status(thm)],[c_2674,c_3490]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_3787,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/0.87      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 4.04/0.87      | k1_xboole_0 != k1_xboole_0 ),
% 4.04/0.87      inference(light_normalisation,[status(thm)],[c_3786,c_2769,c_2898]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_3788,plain,
% 4.04/0.87      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/0.87      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 4.04/0.87      inference(equality_resolution_simp,[status(thm)],[c_3787]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_38,plain,
% 4.04/0.87      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_29,negated_conjecture,
% 4.04/0.87      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 4.04/0.87      inference(cnf_transformation,[],[f70]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(c_36,plain,
% 4.04/0.87      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 4.04/0.87      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.04/0.87  
% 4.04/0.87  cnf(contradiction,plain,
% 4.04/0.87      ( $false ),
% 4.04/0.87      inference(minisat,[status(thm)],[c_12166,c_10103,c_3788,c_38,c_36]) ).
% 4.04/0.87  
% 4.04/0.87  
% 4.04/0.87  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/0.87  
% 4.04/0.87  ------                               Statistics
% 4.04/0.87  
% 4.04/0.87  ------ Selected
% 4.04/0.87  
% 4.04/0.87  total_time:                             0.473
% 4.04/0.87  
%------------------------------------------------------------------------------
