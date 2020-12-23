%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:30 EST 2020

% Result     : Theorem 4.04s
% Output     : CNFRefutation 4.04s
% Verified   : 
% Statistics : Number of formulae       :  176 (1377 expanded)
%              Number of clauses        :  100 ( 318 expanded)
%              Number of leaves         :   20 ( 536 expanded)
%              Depth                    :   20
%              Number of atoms          : 1002 (16671 expanded)
%              Number of equality atoms :  360 (3992 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f47])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f77])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f41,plain,(
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

fof(f40,plain,(
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

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f31,f41,f40,f39,f38,f37,f36])).

fof(f69,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f77])).

fof(f75,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
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
    inference(equality_resolution,[],[f57])).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f74,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
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
    inference(equality_resolution,[],[f58])).

fof(f76,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_228,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_25,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_407,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_408,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_410,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_29,c_27])).

cnf(c_421,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_228,c_410])).

cnf(c_422,plain,
    ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1075,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k2_enumset1(X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1091,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2244,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,sK3)) = k9_subset_1(sK0,X0,sK3) ),
    inference(superposition,[status(thm)],[c_1075,c_1091])).

cnf(c_2324,plain,
    ( k9_subset_1(sK0,sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_422,c_2244])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1081,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1086,plain,
    ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2262,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1086])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1473,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1633,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_1473])).

cnf(c_2514,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2262,c_21,c_19,c_1633])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1078,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2263,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1086])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1478,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1642,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_1478])).

cnf(c_2619,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2263,c_24,c_22,c_1642])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_17,plain,
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
    inference(cnf_transformation,[],[f60])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_166,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_17,c_16,c_15])).

cnf(c_167,plain,
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
    inference(renaming,[status(thm)],[c_166])).

cnf(c_1069,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1090,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1284,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1069,c_1090])).

cnf(c_7223,plain,
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
    inference(superposition,[status(thm)],[c_2619,c_1284])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_33,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_40,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8814,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7223,c_33,c_34,c_39,c_40,c_41])).

cnf(c_8815,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8814])).

cnf(c_8828,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2514,c_8815])).

cnf(c_36,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_42,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_43,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_44,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8911,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8828,c_36,c_42,c_43,c_44])).

cnf(c_8921,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_8911])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1087,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1873,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1087])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1093,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1088,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1092,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2135,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_1092])).

cnf(c_2754,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1093,c_2135])).

cnf(c_2776,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1873,c_2754])).

cnf(c_1874,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1087])).

cnf(c_2777,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1874,c_2754])).

cnf(c_8922,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8921,c_2324,c_2776,c_2777])).

cnf(c_8923,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8922])).

cnf(c_13,plain,
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
    inference(cnf_transformation,[],[f83])).

cnf(c_173,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_17,c_16,c_15])).

cnf(c_174,plain,
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
    inference(renaming,[status(thm)],[c_173])).

cnf(c_1068,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_1256,plain,
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
    inference(forward_subsumption_resolution,[status(thm)],[c_1068,c_1090])).

cnf(c_5416,plain,
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
    inference(superposition,[status(thm)],[c_2619,c_1256])).

cnf(c_7062,plain,
    ( v1_funct_1(X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5416,c_33,c_34,c_39,c_40,c_41])).

cnf(c_7063,plain,
    ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
    | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
    | v1_funct_2(X1,X0,sK1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_7062])).

cnf(c_7076,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2514,c_7063])).

cnf(c_7874,plain,
    ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7076,c_36,c_42,c_43,c_44])).

cnf(c_7884,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2324,c_7874])).

cnf(c_7885,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7884,c_2324,c_2776,c_2777])).

cnf(c_7886,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7885])).

cnf(c_18,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2518,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2514,c_18])).

cnf(c_2623,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2619,c_2518])).

cnf(c_3306,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2324,c_2623])).

cnf(c_3307,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3306,c_2776,c_2777])).

cnf(c_3308,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(equality_resolution_simp,[status(thm)],[c_3307])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8923,c_7886,c_3308,c_37,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 4.04/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.04/1.00  
% 4.04/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.04/1.00  
% 4.04/1.00  ------  iProver source info
% 4.04/1.00  
% 4.04/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.04/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.04/1.00  git: non_committed_changes: false
% 4.04/1.00  git: last_make_outside_of_git: false
% 4.04/1.00  
% 4.04/1.00  ------ 
% 4.04/1.00  
% 4.04/1.00  ------ Input Options
% 4.04/1.00  
% 4.04/1.00  --out_options                           all
% 4.04/1.00  --tptp_safe_out                         true
% 4.04/1.00  --problem_path                          ""
% 4.04/1.00  --include_path                          ""
% 4.04/1.00  --clausifier                            res/vclausify_rel
% 4.04/1.00  --clausifier_options                    --mode clausify
% 4.04/1.00  --stdin                                 false
% 4.04/1.00  --stats_out                             all
% 4.04/1.00  
% 4.04/1.00  ------ General Options
% 4.04/1.00  
% 4.04/1.00  --fof                                   false
% 4.04/1.00  --time_out_real                         305.
% 4.04/1.00  --time_out_virtual                      -1.
% 4.04/1.00  --symbol_type_check                     false
% 4.04/1.00  --clausify_out                          false
% 4.04/1.00  --sig_cnt_out                           false
% 4.04/1.00  --trig_cnt_out                          false
% 4.04/1.00  --trig_cnt_out_tolerance                1.
% 4.04/1.00  --trig_cnt_out_sk_spl                   false
% 4.04/1.00  --abstr_cl_out                          false
% 4.04/1.00  
% 4.04/1.00  ------ Global Options
% 4.04/1.00  
% 4.04/1.00  --schedule                              default
% 4.04/1.00  --add_important_lit                     false
% 4.04/1.00  --prop_solver_per_cl                    1000
% 4.04/1.00  --min_unsat_core                        false
% 4.04/1.00  --soft_assumptions                      false
% 4.04/1.00  --soft_lemma_size                       3
% 4.04/1.00  --prop_impl_unit_size                   0
% 4.04/1.00  --prop_impl_unit                        []
% 4.04/1.00  --share_sel_clauses                     true
% 4.04/1.00  --reset_solvers                         false
% 4.04/1.00  --bc_imp_inh                            [conj_cone]
% 4.04/1.00  --conj_cone_tolerance                   3.
% 4.04/1.00  --extra_neg_conj                        none
% 4.04/1.00  --large_theory_mode                     true
% 4.04/1.00  --prolific_symb_bound                   200
% 4.04/1.00  --lt_threshold                          2000
% 4.04/1.00  --clause_weak_htbl                      true
% 4.04/1.00  --gc_record_bc_elim                     false
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing Options
% 4.04/1.00  
% 4.04/1.00  --preprocessing_flag                    true
% 4.04/1.00  --time_out_prep_mult                    0.1
% 4.04/1.00  --splitting_mode                        input
% 4.04/1.00  --splitting_grd                         true
% 4.04/1.00  --splitting_cvd                         false
% 4.04/1.00  --splitting_cvd_svl                     false
% 4.04/1.00  --splitting_nvd                         32
% 4.04/1.00  --sub_typing                            true
% 4.04/1.00  --prep_gs_sim                           true
% 4.04/1.00  --prep_unflatten                        true
% 4.04/1.00  --prep_res_sim                          true
% 4.04/1.00  --prep_upred                            true
% 4.04/1.00  --prep_sem_filter                       exhaustive
% 4.04/1.00  --prep_sem_filter_out                   false
% 4.04/1.00  --pred_elim                             true
% 4.04/1.00  --res_sim_input                         true
% 4.04/1.00  --eq_ax_congr_red                       true
% 4.04/1.00  --pure_diseq_elim                       true
% 4.04/1.00  --brand_transform                       false
% 4.04/1.00  --non_eq_to_eq                          false
% 4.04/1.00  --prep_def_merge                        true
% 4.04/1.00  --prep_def_merge_prop_impl              false
% 4.04/1.00  --prep_def_merge_mbd                    true
% 4.04/1.00  --prep_def_merge_tr_red                 false
% 4.04/1.00  --prep_def_merge_tr_cl                  false
% 4.04/1.00  --smt_preprocessing                     true
% 4.04/1.00  --smt_ac_axioms                         fast
% 4.04/1.00  --preprocessed_out                      false
% 4.04/1.00  --preprocessed_stats                    false
% 4.04/1.00  
% 4.04/1.00  ------ Abstraction refinement Options
% 4.04/1.00  
% 4.04/1.00  --abstr_ref                             []
% 4.04/1.00  --abstr_ref_prep                        false
% 4.04/1.00  --abstr_ref_until_sat                   false
% 4.04/1.00  --abstr_ref_sig_restrict                funpre
% 4.04/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.00  --abstr_ref_under                       []
% 4.04/1.00  
% 4.04/1.00  ------ SAT Options
% 4.04/1.00  
% 4.04/1.00  --sat_mode                              false
% 4.04/1.00  --sat_fm_restart_options                ""
% 4.04/1.00  --sat_gr_def                            false
% 4.04/1.00  --sat_epr_types                         true
% 4.04/1.00  --sat_non_cyclic_types                  false
% 4.04/1.00  --sat_finite_models                     false
% 4.04/1.00  --sat_fm_lemmas                         false
% 4.04/1.00  --sat_fm_prep                           false
% 4.04/1.00  --sat_fm_uc_incr                        true
% 4.04/1.00  --sat_out_model                         small
% 4.04/1.00  --sat_out_clauses                       false
% 4.04/1.00  
% 4.04/1.00  ------ QBF Options
% 4.04/1.00  
% 4.04/1.00  --qbf_mode                              false
% 4.04/1.00  --qbf_elim_univ                         false
% 4.04/1.00  --qbf_dom_inst                          none
% 4.04/1.00  --qbf_dom_pre_inst                      false
% 4.04/1.00  --qbf_sk_in                             false
% 4.04/1.00  --qbf_pred_elim                         true
% 4.04/1.00  --qbf_split                             512
% 4.04/1.00  
% 4.04/1.00  ------ BMC1 Options
% 4.04/1.00  
% 4.04/1.00  --bmc1_incremental                      false
% 4.04/1.00  --bmc1_axioms                           reachable_all
% 4.04/1.00  --bmc1_min_bound                        0
% 4.04/1.00  --bmc1_max_bound                        -1
% 4.04/1.00  --bmc1_max_bound_default                -1
% 4.04/1.00  --bmc1_symbol_reachability              true
% 4.04/1.00  --bmc1_property_lemmas                  false
% 4.04/1.00  --bmc1_k_induction                      false
% 4.04/1.00  --bmc1_non_equiv_states                 false
% 4.04/1.00  --bmc1_deadlock                         false
% 4.04/1.00  --bmc1_ucm                              false
% 4.04/1.00  --bmc1_add_unsat_core                   none
% 4.04/1.00  --bmc1_unsat_core_children              false
% 4.04/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.00  --bmc1_out_stat                         full
% 4.04/1.00  --bmc1_ground_init                      false
% 4.04/1.00  --bmc1_pre_inst_next_state              false
% 4.04/1.00  --bmc1_pre_inst_state                   false
% 4.04/1.00  --bmc1_pre_inst_reach_state             false
% 4.04/1.00  --bmc1_out_unsat_core                   false
% 4.04/1.00  --bmc1_aig_witness_out                  false
% 4.04/1.00  --bmc1_verbose                          false
% 4.04/1.00  --bmc1_dump_clauses_tptp                false
% 4.04/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.00  --bmc1_dump_file                        -
% 4.04/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.00  --bmc1_ucm_extend_mode                  1
% 4.04/1.00  --bmc1_ucm_init_mode                    2
% 4.04/1.00  --bmc1_ucm_cone_mode                    none
% 4.04/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.00  --bmc1_ucm_relax_model                  4
% 4.04/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.00  --bmc1_ucm_layered_model                none
% 4.04/1.00  --bmc1_ucm_max_lemma_size               10
% 4.04/1.00  
% 4.04/1.00  ------ AIG Options
% 4.04/1.00  
% 4.04/1.00  --aig_mode                              false
% 4.04/1.00  
% 4.04/1.00  ------ Instantiation Options
% 4.04/1.00  
% 4.04/1.00  --instantiation_flag                    true
% 4.04/1.00  --inst_sos_flag                         false
% 4.04/1.00  --inst_sos_phase                        true
% 4.04/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel_side                     num_symb
% 4.04/1.00  --inst_solver_per_active                1400
% 4.04/1.00  --inst_solver_calls_frac                1.
% 4.04/1.00  --inst_passive_queue_type               priority_queues
% 4.04/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.00  --inst_passive_queues_freq              [25;2]
% 4.04/1.00  --inst_dismatching                      true
% 4.04/1.00  --inst_eager_unprocessed_to_passive     true
% 4.04/1.00  --inst_prop_sim_given                   true
% 4.04/1.00  --inst_prop_sim_new                     false
% 4.04/1.00  --inst_subs_new                         false
% 4.04/1.00  --inst_eq_res_simp                      false
% 4.04/1.00  --inst_subs_given                       false
% 4.04/1.00  --inst_orphan_elimination               true
% 4.04/1.00  --inst_learning_loop_flag               true
% 4.04/1.00  --inst_learning_start                   3000
% 4.04/1.00  --inst_learning_factor                  2
% 4.04/1.00  --inst_start_prop_sim_after_learn       3
% 4.04/1.00  --inst_sel_renew                        solver
% 4.04/1.00  --inst_lit_activity_flag                true
% 4.04/1.00  --inst_restr_to_given                   false
% 4.04/1.00  --inst_activity_threshold               500
% 4.04/1.00  --inst_out_proof                        true
% 4.04/1.00  
% 4.04/1.00  ------ Resolution Options
% 4.04/1.00  
% 4.04/1.00  --resolution_flag                       true
% 4.04/1.00  --res_lit_sel                           adaptive
% 4.04/1.00  --res_lit_sel_side                      none
% 4.04/1.00  --res_ordering                          kbo
% 4.04/1.00  --res_to_prop_solver                    active
% 4.04/1.00  --res_prop_simpl_new                    false
% 4.04/1.00  --res_prop_simpl_given                  true
% 4.04/1.00  --res_passive_queue_type                priority_queues
% 4.04/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.00  --res_passive_queues_freq               [15;5]
% 4.04/1.00  --res_forward_subs                      full
% 4.04/1.00  --res_backward_subs                     full
% 4.04/1.00  --res_forward_subs_resolution           true
% 4.04/1.00  --res_backward_subs_resolution          true
% 4.04/1.00  --res_orphan_elimination                true
% 4.04/1.00  --res_time_limit                        2.
% 4.04/1.00  --res_out_proof                         true
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Options
% 4.04/1.00  
% 4.04/1.00  --superposition_flag                    true
% 4.04/1.00  --sup_passive_queue_type                priority_queues
% 4.04/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.04/1.00  --demod_completeness_check              fast
% 4.04/1.00  --demod_use_ground                      true
% 4.04/1.00  --sup_to_prop_solver                    passive
% 4.04/1.00  --sup_prop_simpl_new                    true
% 4.04/1.00  --sup_prop_simpl_given                  true
% 4.04/1.00  --sup_fun_splitting                     false
% 4.04/1.00  --sup_smt_interval                      50000
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Simplification Setup
% 4.04/1.00  
% 4.04/1.00  --sup_indices_passive                   []
% 4.04/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_full_bw                           [BwDemod]
% 4.04/1.00  --sup_immed_triv                        [TrivRules]
% 4.04/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_immed_bw_main                     []
% 4.04/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  
% 4.04/1.00  ------ Combination Options
% 4.04/1.00  
% 4.04/1.00  --comb_res_mult                         3
% 4.04/1.00  --comb_sup_mult                         2
% 4.04/1.00  --comb_inst_mult                        10
% 4.04/1.00  
% 4.04/1.00  ------ Debug Options
% 4.04/1.00  
% 4.04/1.00  --dbg_backtrace                         false
% 4.04/1.00  --dbg_dump_prop_clauses                 false
% 4.04/1.00  --dbg_dump_prop_clauses_file            -
% 4.04/1.00  --dbg_out_stat                          false
% 4.04/1.00  ------ Parsing...
% 4.04/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.04/1.00  ------ Proving...
% 4.04/1.00  ------ Problem Properties 
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  clauses                                 28
% 4.04/1.00  conjectures                             13
% 4.04/1.00  EPR                                     10
% 4.04/1.00  Horn                                    22
% 4.04/1.00  unary                                   14
% 4.04/1.00  binary                                  3
% 4.04/1.00  lits                                    119
% 4.04/1.00  lits eq                                 13
% 4.04/1.00  fd_pure                                 0
% 4.04/1.00  fd_pseudo                               0
% 4.04/1.00  fd_cond                                 1
% 4.04/1.00  fd_pseudo_cond                          0
% 4.04/1.00  AC symbols                              0
% 4.04/1.00  
% 4.04/1.00  ------ Schedule dynamic 5 is on 
% 4.04/1.00  
% 4.04/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  ------ 
% 4.04/1.00  Current options:
% 4.04/1.00  ------ 
% 4.04/1.00  
% 4.04/1.00  ------ Input Options
% 4.04/1.00  
% 4.04/1.00  --out_options                           all
% 4.04/1.00  --tptp_safe_out                         true
% 4.04/1.00  --problem_path                          ""
% 4.04/1.00  --include_path                          ""
% 4.04/1.00  --clausifier                            res/vclausify_rel
% 4.04/1.00  --clausifier_options                    --mode clausify
% 4.04/1.00  --stdin                                 false
% 4.04/1.00  --stats_out                             all
% 4.04/1.00  
% 4.04/1.00  ------ General Options
% 4.04/1.00  
% 4.04/1.00  --fof                                   false
% 4.04/1.00  --time_out_real                         305.
% 4.04/1.00  --time_out_virtual                      -1.
% 4.04/1.00  --symbol_type_check                     false
% 4.04/1.00  --clausify_out                          false
% 4.04/1.00  --sig_cnt_out                           false
% 4.04/1.00  --trig_cnt_out                          false
% 4.04/1.00  --trig_cnt_out_tolerance                1.
% 4.04/1.00  --trig_cnt_out_sk_spl                   false
% 4.04/1.00  --abstr_cl_out                          false
% 4.04/1.00  
% 4.04/1.00  ------ Global Options
% 4.04/1.00  
% 4.04/1.00  --schedule                              default
% 4.04/1.00  --add_important_lit                     false
% 4.04/1.00  --prop_solver_per_cl                    1000
% 4.04/1.00  --min_unsat_core                        false
% 4.04/1.00  --soft_assumptions                      false
% 4.04/1.00  --soft_lemma_size                       3
% 4.04/1.00  --prop_impl_unit_size                   0
% 4.04/1.00  --prop_impl_unit                        []
% 4.04/1.00  --share_sel_clauses                     true
% 4.04/1.00  --reset_solvers                         false
% 4.04/1.00  --bc_imp_inh                            [conj_cone]
% 4.04/1.00  --conj_cone_tolerance                   3.
% 4.04/1.00  --extra_neg_conj                        none
% 4.04/1.00  --large_theory_mode                     true
% 4.04/1.00  --prolific_symb_bound                   200
% 4.04/1.00  --lt_threshold                          2000
% 4.04/1.00  --clause_weak_htbl                      true
% 4.04/1.00  --gc_record_bc_elim                     false
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing Options
% 4.04/1.00  
% 4.04/1.00  --preprocessing_flag                    true
% 4.04/1.00  --time_out_prep_mult                    0.1
% 4.04/1.00  --splitting_mode                        input
% 4.04/1.00  --splitting_grd                         true
% 4.04/1.00  --splitting_cvd                         false
% 4.04/1.00  --splitting_cvd_svl                     false
% 4.04/1.00  --splitting_nvd                         32
% 4.04/1.00  --sub_typing                            true
% 4.04/1.00  --prep_gs_sim                           true
% 4.04/1.00  --prep_unflatten                        true
% 4.04/1.00  --prep_res_sim                          true
% 4.04/1.00  --prep_upred                            true
% 4.04/1.00  --prep_sem_filter                       exhaustive
% 4.04/1.00  --prep_sem_filter_out                   false
% 4.04/1.00  --pred_elim                             true
% 4.04/1.00  --res_sim_input                         true
% 4.04/1.00  --eq_ax_congr_red                       true
% 4.04/1.00  --pure_diseq_elim                       true
% 4.04/1.00  --brand_transform                       false
% 4.04/1.00  --non_eq_to_eq                          false
% 4.04/1.00  --prep_def_merge                        true
% 4.04/1.00  --prep_def_merge_prop_impl              false
% 4.04/1.00  --prep_def_merge_mbd                    true
% 4.04/1.00  --prep_def_merge_tr_red                 false
% 4.04/1.00  --prep_def_merge_tr_cl                  false
% 4.04/1.00  --smt_preprocessing                     true
% 4.04/1.00  --smt_ac_axioms                         fast
% 4.04/1.00  --preprocessed_out                      false
% 4.04/1.00  --preprocessed_stats                    false
% 4.04/1.00  
% 4.04/1.00  ------ Abstraction refinement Options
% 4.04/1.00  
% 4.04/1.00  --abstr_ref                             []
% 4.04/1.00  --abstr_ref_prep                        false
% 4.04/1.00  --abstr_ref_until_sat                   false
% 4.04/1.00  --abstr_ref_sig_restrict                funpre
% 4.04/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.04/1.00  --abstr_ref_under                       []
% 4.04/1.00  
% 4.04/1.00  ------ SAT Options
% 4.04/1.00  
% 4.04/1.00  --sat_mode                              false
% 4.04/1.00  --sat_fm_restart_options                ""
% 4.04/1.00  --sat_gr_def                            false
% 4.04/1.00  --sat_epr_types                         true
% 4.04/1.00  --sat_non_cyclic_types                  false
% 4.04/1.00  --sat_finite_models                     false
% 4.04/1.00  --sat_fm_lemmas                         false
% 4.04/1.00  --sat_fm_prep                           false
% 4.04/1.00  --sat_fm_uc_incr                        true
% 4.04/1.00  --sat_out_model                         small
% 4.04/1.00  --sat_out_clauses                       false
% 4.04/1.00  
% 4.04/1.00  ------ QBF Options
% 4.04/1.00  
% 4.04/1.00  --qbf_mode                              false
% 4.04/1.00  --qbf_elim_univ                         false
% 4.04/1.00  --qbf_dom_inst                          none
% 4.04/1.00  --qbf_dom_pre_inst                      false
% 4.04/1.00  --qbf_sk_in                             false
% 4.04/1.00  --qbf_pred_elim                         true
% 4.04/1.00  --qbf_split                             512
% 4.04/1.00  
% 4.04/1.00  ------ BMC1 Options
% 4.04/1.00  
% 4.04/1.00  --bmc1_incremental                      false
% 4.04/1.00  --bmc1_axioms                           reachable_all
% 4.04/1.00  --bmc1_min_bound                        0
% 4.04/1.00  --bmc1_max_bound                        -1
% 4.04/1.00  --bmc1_max_bound_default                -1
% 4.04/1.00  --bmc1_symbol_reachability              true
% 4.04/1.00  --bmc1_property_lemmas                  false
% 4.04/1.00  --bmc1_k_induction                      false
% 4.04/1.00  --bmc1_non_equiv_states                 false
% 4.04/1.00  --bmc1_deadlock                         false
% 4.04/1.00  --bmc1_ucm                              false
% 4.04/1.00  --bmc1_add_unsat_core                   none
% 4.04/1.00  --bmc1_unsat_core_children              false
% 4.04/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 4.04/1.00  --bmc1_out_stat                         full
% 4.04/1.00  --bmc1_ground_init                      false
% 4.04/1.00  --bmc1_pre_inst_next_state              false
% 4.04/1.00  --bmc1_pre_inst_state                   false
% 4.04/1.00  --bmc1_pre_inst_reach_state             false
% 4.04/1.00  --bmc1_out_unsat_core                   false
% 4.04/1.00  --bmc1_aig_witness_out                  false
% 4.04/1.00  --bmc1_verbose                          false
% 4.04/1.00  --bmc1_dump_clauses_tptp                false
% 4.04/1.00  --bmc1_dump_unsat_core_tptp             false
% 4.04/1.00  --bmc1_dump_file                        -
% 4.04/1.00  --bmc1_ucm_expand_uc_limit              128
% 4.04/1.00  --bmc1_ucm_n_expand_iterations          6
% 4.04/1.00  --bmc1_ucm_extend_mode                  1
% 4.04/1.00  --bmc1_ucm_init_mode                    2
% 4.04/1.00  --bmc1_ucm_cone_mode                    none
% 4.04/1.00  --bmc1_ucm_reduced_relation_type        0
% 4.04/1.00  --bmc1_ucm_relax_model                  4
% 4.04/1.00  --bmc1_ucm_full_tr_after_sat            true
% 4.04/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 4.04/1.00  --bmc1_ucm_layered_model                none
% 4.04/1.00  --bmc1_ucm_max_lemma_size               10
% 4.04/1.00  
% 4.04/1.00  ------ AIG Options
% 4.04/1.00  
% 4.04/1.00  --aig_mode                              false
% 4.04/1.00  
% 4.04/1.00  ------ Instantiation Options
% 4.04/1.00  
% 4.04/1.00  --instantiation_flag                    true
% 4.04/1.00  --inst_sos_flag                         false
% 4.04/1.00  --inst_sos_phase                        true
% 4.04/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.04/1.00  --inst_lit_sel_side                     none
% 4.04/1.00  --inst_solver_per_active                1400
% 4.04/1.00  --inst_solver_calls_frac                1.
% 4.04/1.00  --inst_passive_queue_type               priority_queues
% 4.04/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.04/1.00  --inst_passive_queues_freq              [25;2]
% 4.04/1.00  --inst_dismatching                      true
% 4.04/1.00  --inst_eager_unprocessed_to_passive     true
% 4.04/1.00  --inst_prop_sim_given                   true
% 4.04/1.00  --inst_prop_sim_new                     false
% 4.04/1.00  --inst_subs_new                         false
% 4.04/1.00  --inst_eq_res_simp                      false
% 4.04/1.00  --inst_subs_given                       false
% 4.04/1.00  --inst_orphan_elimination               true
% 4.04/1.00  --inst_learning_loop_flag               true
% 4.04/1.00  --inst_learning_start                   3000
% 4.04/1.00  --inst_learning_factor                  2
% 4.04/1.00  --inst_start_prop_sim_after_learn       3
% 4.04/1.00  --inst_sel_renew                        solver
% 4.04/1.00  --inst_lit_activity_flag                true
% 4.04/1.00  --inst_restr_to_given                   false
% 4.04/1.00  --inst_activity_threshold               500
% 4.04/1.00  --inst_out_proof                        true
% 4.04/1.00  
% 4.04/1.00  ------ Resolution Options
% 4.04/1.00  
% 4.04/1.00  --resolution_flag                       false
% 4.04/1.00  --res_lit_sel                           adaptive
% 4.04/1.00  --res_lit_sel_side                      none
% 4.04/1.00  --res_ordering                          kbo
% 4.04/1.00  --res_to_prop_solver                    active
% 4.04/1.00  --res_prop_simpl_new                    false
% 4.04/1.00  --res_prop_simpl_given                  true
% 4.04/1.00  --res_passive_queue_type                priority_queues
% 4.04/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.04/1.00  --res_passive_queues_freq               [15;5]
% 4.04/1.00  --res_forward_subs                      full
% 4.04/1.00  --res_backward_subs                     full
% 4.04/1.00  --res_forward_subs_resolution           true
% 4.04/1.00  --res_backward_subs_resolution          true
% 4.04/1.00  --res_orphan_elimination                true
% 4.04/1.00  --res_time_limit                        2.
% 4.04/1.00  --res_out_proof                         true
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Options
% 4.04/1.00  
% 4.04/1.00  --superposition_flag                    true
% 4.04/1.00  --sup_passive_queue_type                priority_queues
% 4.04/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.04/1.00  --sup_passive_queues_freq               [8;1;4]
% 4.04/1.00  --demod_completeness_check              fast
% 4.04/1.00  --demod_use_ground                      true
% 4.04/1.00  --sup_to_prop_solver                    passive
% 4.04/1.00  --sup_prop_simpl_new                    true
% 4.04/1.00  --sup_prop_simpl_given                  true
% 4.04/1.00  --sup_fun_splitting                     false
% 4.04/1.00  --sup_smt_interval                      50000
% 4.04/1.00  
% 4.04/1.00  ------ Superposition Simplification Setup
% 4.04/1.00  
% 4.04/1.00  --sup_indices_passive                   []
% 4.04/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.04/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 4.04/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_full_bw                           [BwDemod]
% 4.04/1.00  --sup_immed_triv                        [TrivRules]
% 4.04/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.04/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_immed_bw_main                     []
% 4.04/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 4.04/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.04/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.04/1.00  
% 4.04/1.00  ------ Combination Options
% 4.04/1.00  
% 4.04/1.00  --comb_res_mult                         3
% 4.04/1.00  --comb_sup_mult                         2
% 4.04/1.00  --comb_inst_mult                        10
% 4.04/1.00  
% 4.04/1.00  ------ Debug Options
% 4.04/1.00  
% 4.04/1.00  --dbg_backtrace                         false
% 4.04/1.00  --dbg_dump_prop_clauses                 false
% 4.04/1.00  --dbg_dump_prop_clauses_file            -
% 4.04/1.00  --dbg_out_stat                          false
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  ------ Proving...
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  % SZS status Theorem for theBenchmark.p
% 4.04/1.00  
% 4.04/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.04/1.00  
% 4.04/1.00  fof(f1,axiom,(
% 4.04/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f32,plain,(
% 4.04/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 4.04/1.00    inference(nnf_transformation,[],[f1])).
% 4.04/1.00  
% 4.04/1.00  fof(f43,plain,(
% 4.04/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f32])).
% 4.04/1.00  
% 4.04/1.00  fof(f7,axiom,(
% 4.04/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f50,plain,(
% 4.04/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f7])).
% 4.04/1.00  
% 4.04/1.00  fof(f4,axiom,(
% 4.04/1.00    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f47,plain,(
% 4.04/1.00    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f4])).
% 4.04/1.00  
% 4.04/1.00  fof(f77,plain,(
% 4.04/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 4.04/1.00    inference(definition_unfolding,[],[f50,f47])).
% 4.04/1.00  
% 4.04/1.00  fof(f79,plain,(
% 4.04/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.04/1.00    inference(definition_unfolding,[],[f43,f77])).
% 4.04/1.00  
% 4.04/1.00  fof(f9,axiom,(
% 4.04/1.00    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f21,plain,(
% 4.04/1.00    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 4.04/1.00    inference(ennf_transformation,[],[f9])).
% 4.04/1.00  
% 4.04/1.00  fof(f22,plain,(
% 4.04/1.00    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 4.04/1.00    inference(flattening,[],[f21])).
% 4.04/1.00  
% 4.04/1.00  fof(f33,plain,(
% 4.04/1.00    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 4.04/1.00    inference(nnf_transformation,[],[f22])).
% 4.04/1.00  
% 4.04/1.00  fof(f53,plain,(
% 4.04/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f33])).
% 4.04/1.00  
% 4.04/1.00  fof(f14,conjecture,(
% 4.04/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f15,negated_conjecture,(
% 4.04/1.00    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 4.04/1.00    inference(negated_conjecture,[],[f14])).
% 4.04/1.00  
% 4.04/1.00  fof(f30,plain,(
% 4.04/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 4.04/1.00    inference(ennf_transformation,[],[f15])).
% 4.04/1.00  
% 4.04/1.00  fof(f31,plain,(
% 4.04/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 4.04/1.00    inference(flattening,[],[f30])).
% 4.04/1.00  
% 4.04/1.00  fof(f41,plain,(
% 4.04/1.00    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f40,plain,(
% 4.04/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f39,plain,(
% 4.04/1.00    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f38,plain,(
% 4.04/1.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f37,plain,(
% 4.04/1.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f36,plain,(
% 4.04/1.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 4.04/1.00    introduced(choice_axiom,[])).
% 4.04/1.00  
% 4.04/1.00  fof(f42,plain,(
% 4.04/1.00    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 4.04/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f31,f41,f40,f39,f38,f37,f36])).
% 4.04/1.00  
% 4.04/1.00  fof(f69,plain,(
% 4.04/1.00    r1_subset_1(sK2,sK3)),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f65,plain,(
% 4.04/1.00    ~v1_xboole_0(sK2)),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f67,plain,(
% 4.04/1.00    ~v1_xboole_0(sK3)),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f68,plain,(
% 4.04/1.00    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f5,axiom,(
% 4.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f17,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 4.04/1.00    inference(ennf_transformation,[],[f5])).
% 4.04/1.00  
% 4.04/1.00  fof(f48,plain,(
% 4.04/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f17])).
% 4.04/1.00  
% 4.04/1.00  fof(f80,plain,(
% 4.04/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 4.04/1.00    inference(definition_unfolding,[],[f48,f77])).
% 4.04/1.00  
% 4.04/1.00  fof(f75,plain,(
% 4.04/1.00    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f11,axiom,(
% 4.04/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f24,plain,(
% 4.04/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.04/1.00    inference(ennf_transformation,[],[f11])).
% 4.04/1.00  
% 4.04/1.00  fof(f25,plain,(
% 4.04/1.00    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.04/1.00    inference(flattening,[],[f24])).
% 4.04/1.00  
% 4.04/1.00  fof(f56,plain,(
% 4.04/1.00    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f25])).
% 4.04/1.00  
% 4.04/1.00  fof(f73,plain,(
% 4.04/1.00    v1_funct_1(sK5)),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f72,plain,(
% 4.04/1.00    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f70,plain,(
% 4.04/1.00    v1_funct_1(sK4)),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f12,axiom,(
% 4.04/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f26,plain,(
% 4.04/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.04/1.00    inference(ennf_transformation,[],[f12])).
% 4.04/1.00  
% 4.04/1.00  fof(f27,plain,(
% 4.04/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.04/1.00    inference(flattening,[],[f26])).
% 4.04/1.00  
% 4.04/1.00  fof(f34,plain,(
% 4.04/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.04/1.00    inference(nnf_transformation,[],[f27])).
% 4.04/1.00  
% 4.04/1.00  fof(f35,plain,(
% 4.04/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 4.04/1.00    inference(flattening,[],[f34])).
% 4.04/1.00  
% 4.04/1.00  fof(f57,plain,(
% 4.04/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f35])).
% 4.04/1.00  
% 4.04/1.00  fof(f84,plain,(
% 4.04/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/1.00    inference(equality_resolution,[],[f57])).
% 4.04/1.00  
% 4.04/1.00  fof(f13,axiom,(
% 4.04/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f28,plain,(
% 4.04/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 4.04/1.00    inference(ennf_transformation,[],[f13])).
% 4.04/1.00  
% 4.04/1.00  fof(f29,plain,(
% 4.04/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 4.04/1.00    inference(flattening,[],[f28])).
% 4.04/1.00  
% 4.04/1.00  fof(f60,plain,(
% 4.04/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f29])).
% 4.04/1.00  
% 4.04/1.00  fof(f61,plain,(
% 4.04/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f29])).
% 4.04/1.00  
% 4.04/1.00  fof(f62,plain,(
% 4.04/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f29])).
% 4.04/1.00  
% 4.04/1.00  fof(f6,axiom,(
% 4.04/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f18,plain,(
% 4.04/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 4.04/1.00    inference(ennf_transformation,[],[f6])).
% 4.04/1.00  
% 4.04/1.00  fof(f49,plain,(
% 4.04/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f18])).
% 4.04/1.00  
% 4.04/1.00  fof(f64,plain,(
% 4.04/1.00    ~v1_xboole_0(sK1)),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f71,plain,(
% 4.04/1.00    v1_funct_2(sK4,sK2,sK1)),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f74,plain,(
% 4.04/1.00    v1_funct_2(sK5,sK3,sK1)),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f10,axiom,(
% 4.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f23,plain,(
% 4.04/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.04/1.00    inference(ennf_transformation,[],[f10])).
% 4.04/1.00  
% 4.04/1.00  fof(f55,plain,(
% 4.04/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.04/1.00    inference(cnf_transformation,[],[f23])).
% 4.04/1.00  
% 4.04/1.00  fof(f2,axiom,(
% 4.04/1.00    v1_xboole_0(k1_xboole_0)),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f45,plain,(
% 4.04/1.00    v1_xboole_0(k1_xboole_0)),
% 4.04/1.00    inference(cnf_transformation,[],[f2])).
% 4.04/1.00  
% 4.04/1.00  fof(f8,axiom,(
% 4.04/1.00    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f19,plain,(
% 4.04/1.00    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 4.04/1.00    inference(ennf_transformation,[],[f8])).
% 4.04/1.00  
% 4.04/1.00  fof(f20,plain,(
% 4.04/1.00    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 4.04/1.00    inference(flattening,[],[f19])).
% 4.04/1.00  
% 4.04/1.00  fof(f51,plain,(
% 4.04/1.00    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X1) | ~v1_relat_1(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f20])).
% 4.04/1.00  
% 4.04/1.00  fof(f3,axiom,(
% 4.04/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 4.04/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.04/1.00  
% 4.04/1.00  fof(f16,plain,(
% 4.04/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 4.04/1.00    inference(ennf_transformation,[],[f3])).
% 4.04/1.00  
% 4.04/1.00  fof(f46,plain,(
% 4.04/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f16])).
% 4.04/1.00  
% 4.04/1.00  fof(f58,plain,(
% 4.04/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/1.00    inference(cnf_transformation,[],[f35])).
% 4.04/1.00  
% 4.04/1.00  fof(f83,plain,(
% 4.04/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 4.04/1.00    inference(equality_resolution,[],[f58])).
% 4.04/1.00  
% 4.04/1.00  fof(f76,plain,(
% 4.04/1.00    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  fof(f66,plain,(
% 4.04/1.00    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 4.04/1.00    inference(cnf_transformation,[],[f42])).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1,plain,
% 4.04/1.00      ( ~ r1_xboole_0(X0,X1)
% 4.04/1.00      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
% 4.04/1.00      inference(cnf_transformation,[],[f79]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_228,plain,
% 4.04/1.00      ( ~ r1_xboole_0(X0,X1)
% 4.04/1.00      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0 ),
% 4.04/1.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_9,plain,
% 4.04/1.00      ( ~ r1_subset_1(X0,X1)
% 4.04/1.00      | r1_xboole_0(X0,X1)
% 4.04/1.00      | v1_xboole_0(X0)
% 4.04/1.00      | v1_xboole_0(X1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f53]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_25,negated_conjecture,
% 4.04/1.00      ( r1_subset_1(sK2,sK3) ),
% 4.04/1.00      inference(cnf_transformation,[],[f69]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_407,plain,
% 4.04/1.00      ( r1_xboole_0(X0,X1)
% 4.04/1.00      | v1_xboole_0(X0)
% 4.04/1.00      | v1_xboole_0(X1)
% 4.04/1.00      | sK3 != X1
% 4.04/1.00      | sK2 != X0 ),
% 4.04/1.00      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_408,plain,
% 4.04/1.00      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 4.04/1.00      inference(unflattening,[status(thm)],[c_407]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_29,negated_conjecture,
% 4.04/1.00      ( ~ v1_xboole_0(sK2) ),
% 4.04/1.00      inference(cnf_transformation,[],[f65]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_27,negated_conjecture,
% 4.04/1.00      ( ~ v1_xboole_0(sK3) ),
% 4.04/1.00      inference(cnf_transformation,[],[f67]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_410,plain,
% 4.04/1.00      ( r1_xboole_0(sK2,sK3) ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_408,c_29,c_27]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_421,plain,
% 4.04/1.00      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_xboole_0
% 4.04/1.00      | sK3 != X1
% 4.04/1.00      | sK2 != X0 ),
% 4.04/1.00      inference(resolution_lifted,[status(thm)],[c_228,c_410]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_422,plain,
% 4.04/1.00      ( k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK3)) = k1_xboole_0 ),
% 4.04/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_26,negated_conjecture,
% 4.04/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 4.04/1.00      inference(cnf_transformation,[],[f68]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1075,plain,
% 4.04/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_4,plain,
% 4.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/1.00      | k1_setfam_1(k2_enumset1(X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f80]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1091,plain,
% 4.04/1.00      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 4.04/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2244,plain,
% 4.04/1.00      ( k1_setfam_1(k2_enumset1(X0,X0,X0,sK3)) = k9_subset_1(sK0,X0,sK3) ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1075,c_1091]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2324,plain,
% 4.04/1.00      ( k9_subset_1(sK0,sK2,sK3) = k1_xboole_0 ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_422,c_2244]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_19,negated_conjecture,
% 4.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 4.04/1.00      inference(cnf_transformation,[],[f75]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1081,plain,
% 4.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_11,plain,
% 4.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 4.04/1.00      inference(cnf_transformation,[],[f56]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1086,plain,
% 4.04/1.00      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
% 4.04/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/1.00      | v1_funct_1(X2) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2262,plain,
% 4.04/1.00      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
% 4.04/1.00      | v1_funct_1(sK5) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1081,c_1086]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_21,negated_conjecture,
% 4.04/1.00      ( v1_funct_1(sK5) ),
% 4.04/1.00      inference(cnf_transformation,[],[f73]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1473,plain,
% 4.04/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.04/1.00      | ~ v1_funct_1(sK5)
% 4.04/1.00      | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1633,plain,
% 4.04/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 4.04/1.00      | ~ v1_funct_1(sK5)
% 4.04/1.00      | k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_1473]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2514,plain,
% 4.04/1.00      ( k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0) ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_2262,c_21,c_19,c_1633]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_22,negated_conjecture,
% 4.04/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 4.04/1.00      inference(cnf_transformation,[],[f72]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1078,plain,
% 4.04/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2263,plain,
% 4.04/1.00      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
% 4.04/1.00      | v1_funct_1(sK4) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1078,c_1086]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_24,negated_conjecture,
% 4.04/1.00      ( v1_funct_1(sK4) ),
% 4.04/1.00      inference(cnf_transformation,[],[f70]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1478,plain,
% 4.04/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.04/1.00      | ~ v1_funct_1(sK4)
% 4.04/1.00      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1642,plain,
% 4.04/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 4.04/1.00      | ~ v1_funct_1(sK4)
% 4.04/1.00      | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 4.04/1.00      inference(instantiation,[status(thm)],[c_1478]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2619,plain,
% 4.04/1.00      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_2263,c_24,c_22,c_1642]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_14,plain,
% 4.04/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.00      | ~ v1_funct_2(X3,X4,X2)
% 4.04/1.00      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 4.04/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/1.00      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | ~ v1_funct_1(X3)
% 4.04/1.00      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 4.04/1.00      | v1_xboole_0(X5)
% 4.04/1.00      | v1_xboole_0(X2)
% 4.04/1.00      | v1_xboole_0(X4)
% 4.04/1.00      | v1_xboole_0(X1)
% 4.04/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 4.04/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_17,plain,
% 4.04/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.00      | ~ v1_funct_2(X3,X4,X2)
% 4.04/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | ~ v1_funct_1(X3)
% 4.04/1.00      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 4.04/1.00      | v1_xboole_0(X5)
% 4.04/1.00      | v1_xboole_0(X2)
% 4.04/1.00      | v1_xboole_0(X4)
% 4.04/1.00      | v1_xboole_0(X1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f60]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_16,plain,
% 4.04/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.00      | ~ v1_funct_2(X3,X4,X2)
% 4.04/1.00      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 4.04/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | ~ v1_funct_1(X3)
% 4.04/1.00      | v1_xboole_0(X5)
% 4.04/1.00      | v1_xboole_0(X2)
% 4.04/1.00      | v1_xboole_0(X4)
% 4.04/1.00      | v1_xboole_0(X1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f61]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_15,plain,
% 4.04/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.00      | ~ v1_funct_2(X3,X4,X2)
% 4.04/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/1.00      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | ~ v1_funct_1(X3)
% 4.04/1.00      | v1_xboole_0(X5)
% 4.04/1.00      | v1_xboole_0(X2)
% 4.04/1.00      | v1_xboole_0(X4)
% 4.04/1.00      | v1_xboole_0(X1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f62]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_166,plain,
% 4.04/1.00      ( ~ v1_funct_1(X3)
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | ~ v1_funct_2(X3,X4,X2)
% 4.04/1.00      | ~ v1_funct_2(X0,X1,X2)
% 4.04/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/1.00      | v1_xboole_0(X5)
% 4.04/1.00      | v1_xboole_0(X2)
% 4.04/1.00      | v1_xboole_0(X4)
% 4.04/1.00      | v1_xboole_0(X1)
% 4.04/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_14,c_17,c_16,c_15]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_167,plain,
% 4.04/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.00      | ~ v1_funct_2(X3,X4,X2)
% 4.04/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | ~ v1_funct_1(X3)
% 4.04/1.00      | v1_xboole_0(X1)
% 4.04/1.00      | v1_xboole_0(X2)
% 4.04/1.00      | v1_xboole_0(X4)
% 4.04/1.00      | v1_xboole_0(X5)
% 4.04/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 4.04/1.00      inference(renaming,[status(thm)],[c_166]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1069,plain,
% 4.04/1.00      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X4) = X5
% 4.04/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.04/1.00      | v1_funct_2(X5,X4,X1) != iProver_top
% 4.04/1.00      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 4.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 4.04/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 4.04/1.00      | v1_funct_1(X2) != iProver_top
% 4.04/1.00      | v1_funct_1(X5) != iProver_top
% 4.04/1.00      | v1_xboole_0(X3) = iProver_top
% 4.04/1.00      | v1_xboole_0(X1) = iProver_top
% 4.04/1.00      | v1_xboole_0(X4) = iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_5,plain,
% 4.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.04/1.00      | ~ v1_xboole_0(X1)
% 4.04/1.00      | v1_xboole_0(X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f49]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1090,plain,
% 4.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.04/1.00      | v1_xboole_0(X1) != iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1284,plain,
% 4.04/1.00      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X0) = X2
% 4.04/1.00      | v1_funct_2(X5,X4,X1) != iProver_top
% 4.04/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 4.04/1.00      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 4.04/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 4.04/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/1.00      | v1_funct_1(X5) != iProver_top
% 4.04/1.00      | v1_funct_1(X2) != iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top
% 4.04/1.00      | v1_xboole_0(X1) = iProver_top
% 4.04/1.00      | v1_xboole_0(X4) = iProver_top ),
% 4.04/1.00      inference(forward_subsumption_resolution,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_1069,c_1090]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7223,plain,
% 4.04/1.00      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
% 4.04/1.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/1.00      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 4.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | v1_funct_1(X1) != iProver_top
% 4.04/1.00      | v1_funct_1(sK4) != iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top
% 4.04/1.00      | v1_xboole_0(sK1) = iProver_top
% 4.04/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_2619,c_1284]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_30,negated_conjecture,
% 4.04/1.00      ( ~ v1_xboole_0(sK1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f64]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_33,plain,
% 4.04/1.00      ( v1_xboole_0(sK1) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_34,plain,
% 4.04/1.00      ( v1_xboole_0(sK2) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_39,plain,
% 4.04/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_23,negated_conjecture,
% 4.04/1.00      ( v1_funct_2(sK4,sK2,sK1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f71]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_40,plain,
% 4.04/1.00      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_41,plain,
% 4.04/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8814,plain,
% 4.04/1.00      ( v1_funct_1(X1) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/1.00      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
% 4.04/1.00      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_7223,c_33,c_34,c_39,c_40,c_41]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8815,plain,
% 4.04/1.00      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),sK2) = sK4
% 4.04/1.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | v1_funct_1(X1) != iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top ),
% 4.04/1.00      inference(renaming,[status(thm)],[c_8814]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8828,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 4.04/1.00      | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
% 4.04/1.00      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 4.04/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 4.04/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 4.04/1.00      | v1_funct_1(sK5) != iProver_top
% 4.04/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_2514,c_8815]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_36,plain,
% 4.04/1.00      ( v1_xboole_0(sK3) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_42,plain,
% 4.04/1.00      ( v1_funct_1(sK5) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_20,negated_conjecture,
% 4.04/1.00      ( v1_funct_2(sK5,sK3,sK1) ),
% 4.04/1.00      inference(cnf_transformation,[],[f74]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_43,plain,
% 4.04/1.00      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_44,plain,
% 4.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8911,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 4.04/1.00      | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
% 4.04/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_8828,c_36,c_42,c_43,c_44]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8921,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 4.04/1.00      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 4.04/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_2324,c_8911]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_10,plain,
% 4.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | v1_relat_1(X0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f55]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1087,plain,
% 4.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.04/1.00      | v1_relat_1(X0) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1873,plain,
% 4.04/1.00      ( v1_relat_1(sK5) = iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1081,c_1087]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2,plain,
% 4.04/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 4.04/1.00      inference(cnf_transformation,[],[f45]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1093,plain,
% 4.04/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7,plain,
% 4.04/1.00      ( ~ v1_relat_1(X0)
% 4.04/1.00      | ~ v1_xboole_0(X1)
% 4.04/1.00      | v1_xboole_0(k7_relat_1(X0,X1)) ),
% 4.04/1.00      inference(cnf_transformation,[],[f51]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1088,plain,
% 4.04/1.00      ( v1_relat_1(X0) != iProver_top
% 4.04/1.00      | v1_xboole_0(X1) != iProver_top
% 4.04/1.00      | v1_xboole_0(k7_relat_1(X0,X1)) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3,plain,
% 4.04/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 4.04/1.00      inference(cnf_transformation,[],[f46]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1092,plain,
% 4.04/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2135,plain,
% 4.04/1.00      ( k7_relat_1(X0,X1) = k1_xboole_0
% 4.04/1.00      | v1_relat_1(X0) != iProver_top
% 4.04/1.00      | v1_xboole_0(X1) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1088,c_1092]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2754,plain,
% 4.04/1.00      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 4.04/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1093,c_2135]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2776,plain,
% 4.04/1.00      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1873,c_2754]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1874,plain,
% 4.04/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1078,c_1087]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2777,plain,
% 4.04/1.00      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_1874,c_2754]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8922,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 4.04/1.00      | k1_xboole_0 != k1_xboole_0
% 4.04/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/1.00      inference(light_normalisation,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_8921,c_2324,c_2776,c_2777]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_8923,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 4.04/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/1.00      inference(equality_resolution_simp,[status(thm)],[c_8922]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_13,plain,
% 4.04/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.00      | ~ v1_funct_2(X3,X4,X2)
% 4.04/1.00      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 4.04/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/1.00      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | ~ v1_funct_1(X3)
% 4.04/1.00      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 4.04/1.00      | v1_xboole_0(X5)
% 4.04/1.00      | v1_xboole_0(X2)
% 4.04/1.00      | v1_xboole_0(X4)
% 4.04/1.00      | v1_xboole_0(X1)
% 4.04/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 4.04/1.00      inference(cnf_transformation,[],[f83]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_173,plain,
% 4.04/1.00      ( ~ v1_funct_1(X3)
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | ~ v1_funct_2(X3,X4,X2)
% 4.04/1.00      | ~ v1_funct_2(X0,X1,X2)
% 4.04/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/1.00      | v1_xboole_0(X5)
% 4.04/1.00      | v1_xboole_0(X2)
% 4.04/1.00      | v1_xboole_0(X4)
% 4.04/1.00      | v1_xboole_0(X1)
% 4.04/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_13,c_17,c_16,c_15]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_174,plain,
% 4.04/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.04/1.00      | ~ v1_funct_2(X3,X4,X2)
% 4.04/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 4.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.04/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.04/1.00      | ~ v1_funct_1(X0)
% 4.04/1.00      | ~ v1_funct_1(X3)
% 4.04/1.00      | v1_xboole_0(X1)
% 4.04/1.00      | v1_xboole_0(X2)
% 4.04/1.00      | v1_xboole_0(X4)
% 4.04/1.00      | v1_xboole_0(X5)
% 4.04/1.00      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 4.04/1.00      inference(renaming,[status(thm)],[c_173]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1068,plain,
% 4.04/1.00      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X4,X0)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X4,X0))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X3,X4,X0),X1,k1_tmap_1(X3,X1,X4,X0,X5,X2),X0) = X2
% 4.04/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.04/1.00      | v1_funct_2(X5,X4,X1) != iProver_top
% 4.04/1.00      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 4.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 4.04/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 4.04/1.00      | v1_funct_1(X2) != iProver_top
% 4.04/1.00      | v1_funct_1(X5) != iProver_top
% 4.04/1.00      | v1_xboole_0(X3) = iProver_top
% 4.04/1.00      | v1_xboole_0(X1) = iProver_top
% 4.04/1.00      | v1_xboole_0(X4) = iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_1256,plain,
% 4.04/1.00      ( k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,X5,k9_subset_1(X3,X0,X4))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,X5),X4) = X5
% 4.04/1.00      | v1_funct_2(X5,X4,X1) != iProver_top
% 4.04/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(X3)) != iProver_top
% 4.04/1.00      | m1_subset_1(X4,k1_zfmisc_1(X3)) != iProver_top
% 4.04/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) != iProver_top
% 4.04/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.04/1.00      | v1_funct_1(X5) != iProver_top
% 4.04/1.00      | v1_funct_1(X2) != iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top
% 4.04/1.00      | v1_xboole_0(X1) = iProver_top
% 4.04/1.00      | v1_xboole_0(X4) = iProver_top ),
% 4.04/1.00      inference(forward_subsumption_resolution,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_1068,c_1090]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_5416,plain,
% 4.04/1.00      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 4.04/1.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/1.00      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 4.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | v1_funct_1(X1) != iProver_top
% 4.04/1.00      | v1_funct_1(sK4) != iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top
% 4.04/1.00      | v1_xboole_0(sK1) = iProver_top
% 4.04/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_2619,c_1256]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7062,plain,
% 4.04/1.00      ( v1_funct_1(X1) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/1.00      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 4.04/1.00      | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_5416,c_33,c_34,c_39,c_40,c_41]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7063,plain,
% 4.04/1.00      ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,sK2,X0)) != k7_relat_1(sK4,k9_subset_1(X2,sK2,X0))
% 4.04/1.00      | k2_partfun1(k4_subset_1(X2,sK2,X0),sK1,k1_tmap_1(X2,sK1,sK2,X0,sK4,X1),X0) = X1
% 4.04/1.00      | v1_funct_2(X1,X0,sK1) != iProver_top
% 4.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X2)) != iProver_top
% 4.04/1.00      | v1_funct_1(X1) != iProver_top
% 4.04/1.00      | v1_xboole_0(X0) = iProver_top ),
% 4.04/1.00      inference(renaming,[status(thm)],[c_7062]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7076,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 4.04/1.00      | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
% 4.04/1.00      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 4.04/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 4.04/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top
% 4.04/1.00      | v1_funct_1(sK5) != iProver_top
% 4.04/1.00      | v1_xboole_0(sK3) = iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_2514,c_7063]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7874,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 4.04/1.00      | k7_relat_1(sK4,k9_subset_1(X0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(X0,sK2,sK3))
% 4.04/1.00      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(X0)) != iProver_top ),
% 4.04/1.00      inference(global_propositional_subsumption,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_7076,c_36,c_42,c_43,c_44]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7884,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 4.04/1.00      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 4.04/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/1.00      inference(superposition,[status(thm)],[c_2324,c_7874]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7885,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 4.04/1.00      | k1_xboole_0 != k1_xboole_0
% 4.04/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/1.00      inference(light_normalisation,
% 4.04/1.00                [status(thm)],
% 4.04/1.00                [c_7884,c_2324,c_2776,c_2777]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_7886,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 4.04/1.00      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 4.04/1.00      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 4.04/1.00      inference(equality_resolution_simp,[status(thm)],[c_7885]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_18,negated_conjecture,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/1.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 4.04/1.00      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 4.04/1.00      inference(cnf_transformation,[],[f76]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2518,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/1.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 4.04/1.00      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 4.04/1.00      inference(demodulation,[status(thm)],[c_2514,c_18]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_2623,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/1.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 4.04/1.00      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 4.04/1.00      inference(demodulation,[status(thm)],[c_2619,c_2518]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3306,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/1.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 4.04/1.00      | k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) ),
% 4.04/1.00      inference(demodulation,[status(thm)],[c_2324,c_2623]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3307,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/1.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 4.04/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 4.04/1.00      inference(light_normalisation,[status(thm)],[c_3306,c_2776,c_2777]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_3308,plain,
% 4.04/1.00      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 4.04/1.00      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 4.04/1.00      inference(equality_resolution_simp,[status(thm)],[c_3307]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_37,plain,
% 4.04/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_28,negated_conjecture,
% 4.04/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 4.04/1.00      inference(cnf_transformation,[],[f66]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(c_35,plain,
% 4.04/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 4.04/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.04/1.00  
% 4.04/1.00  cnf(contradiction,plain,
% 4.04/1.00      ( $false ),
% 4.04/1.00      inference(minisat,[status(thm)],[c_8923,c_7886,c_3308,c_37,c_35]) ).
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.04/1.00  
% 4.04/1.00  ------                               Statistics
% 4.04/1.00  
% 4.04/1.00  ------ General
% 4.04/1.00  
% 4.04/1.00  abstr_ref_over_cycles:                  0
% 4.04/1.00  abstr_ref_under_cycles:                 0
% 4.04/1.00  gc_basic_clause_elim:                   0
% 4.04/1.00  forced_gc_time:                         0
% 4.04/1.00  parsing_time:                           0.014
% 4.04/1.00  unif_index_cands_time:                  0.
% 4.04/1.00  unif_index_add_time:                    0.
% 4.04/1.00  orderings_time:                         0.
% 4.04/1.00  out_proof_time:                         0.015
% 4.04/1.00  total_time:                             0.475
% 4.04/1.00  num_of_symbols:                         54
% 4.04/1.00  num_of_terms:                           21483
% 4.04/1.00  
% 4.04/1.00  ------ Preprocessing
% 4.04/1.00  
% 4.04/1.00  num_of_splits:                          0
% 4.04/1.00  num_of_split_atoms:                     0
% 4.04/1.00  num_of_reused_defs:                     0
% 4.04/1.00  num_eq_ax_congr_red:                    12
% 4.04/1.00  num_of_sem_filtered_clauses:            1
% 4.04/1.00  num_of_subtypes:                        0
% 4.04/1.00  monotx_restored_types:                  0
% 4.04/1.00  sat_num_of_epr_types:                   0
% 4.04/1.00  sat_num_of_non_cyclic_types:            0
% 4.04/1.00  sat_guarded_non_collapsed_types:        0
% 4.04/1.00  num_pure_diseq_elim:                    0
% 4.04/1.00  simp_replaced_by:                       0
% 4.04/1.00  res_preprocessed:                       147
% 4.04/1.00  prep_upred:                             0
% 4.04/1.00  prep_unflattend:                        4
% 4.04/1.00  smt_new_axioms:                         0
% 4.04/1.00  pred_elim_cands:                        5
% 4.04/1.00  pred_elim:                              2
% 4.04/1.00  pred_elim_cl:                           4
% 4.04/1.00  pred_elim_cycles:                       4
% 4.04/1.00  merged_defs:                            2
% 4.04/1.00  merged_defs_ncl:                        0
% 4.04/1.00  bin_hyper_res:                          2
% 4.04/1.00  prep_cycles:                            4
% 4.04/1.00  pred_elim_time:                         0.002
% 4.04/1.00  splitting_time:                         0.
% 4.04/1.00  sem_filter_time:                        0.
% 4.04/1.00  monotx_time:                            0.001
% 4.04/1.00  subtype_inf_time:                       0.
% 4.04/1.00  
% 4.04/1.00  ------ Problem properties
% 4.04/1.00  
% 4.04/1.00  clauses:                                28
% 4.04/1.00  conjectures:                            13
% 4.04/1.00  epr:                                    10
% 4.04/1.00  horn:                                   22
% 4.04/1.00  ground:                                 15
% 4.04/1.00  unary:                                  14
% 4.04/1.00  binary:                                 3
% 4.04/1.00  lits:                                   119
% 4.04/1.00  lits_eq:                                13
% 4.04/1.00  fd_pure:                                0
% 4.04/1.00  fd_pseudo:                              0
% 4.04/1.00  fd_cond:                                1
% 4.04/1.00  fd_pseudo_cond:                         0
% 4.04/1.00  ac_symbols:                             0
% 4.04/1.00  
% 4.04/1.00  ------ Propositional Solver
% 4.04/1.00  
% 4.04/1.00  prop_solver_calls:                      27
% 4.04/1.00  prop_fast_solver_calls:                 1769
% 4.04/1.00  smt_solver_calls:                       0
% 4.04/1.00  smt_fast_solver_calls:                  0
% 4.04/1.00  prop_num_of_clauses:                    4019
% 4.04/1.00  prop_preprocess_simplified:             7796
% 4.04/1.00  prop_fo_subsumed:                       74
% 4.04/1.00  prop_solver_time:                       0.
% 4.04/1.00  smt_solver_time:                        0.
% 4.04/1.00  smt_fast_solver_time:                   0.
% 4.04/1.00  prop_fast_solver_time:                  0.
% 4.04/1.00  prop_unsat_core_time:                   0.
% 4.04/1.00  
% 4.04/1.00  ------ QBF
% 4.04/1.00  
% 4.04/1.00  qbf_q_res:                              0
% 4.04/1.00  qbf_num_tautologies:                    0
% 4.04/1.00  qbf_prep_cycles:                        0
% 4.04/1.00  
% 4.04/1.00  ------ BMC1
% 4.04/1.00  
% 4.04/1.00  bmc1_current_bound:                     -1
% 4.04/1.00  bmc1_last_solved_bound:                 -1
% 4.04/1.00  bmc1_unsat_core_size:                   -1
% 4.04/1.00  bmc1_unsat_core_parents_size:           -1
% 4.04/1.00  bmc1_merge_next_fun:                    0
% 4.04/1.00  bmc1_unsat_core_clauses_time:           0.
% 4.04/1.00  
% 4.04/1.00  ------ Instantiation
% 4.04/1.00  
% 4.04/1.00  inst_num_of_clauses:                    1027
% 4.04/1.00  inst_num_in_passive:                    219
% 4.04/1.00  inst_num_in_active:                     521
% 4.04/1.00  inst_num_in_unprocessed:                287
% 4.04/1.00  inst_num_of_loops:                      530
% 4.04/1.00  inst_num_of_learning_restarts:          0
% 4.04/1.00  inst_num_moves_active_passive:          5
% 4.04/1.00  inst_lit_activity:                      0
% 4.04/1.00  inst_lit_activity_moves:                0
% 4.04/1.00  inst_num_tautologies:                   0
% 4.04/1.00  inst_num_prop_implied:                  0
% 4.04/1.00  inst_num_existing_simplified:           0
% 4.04/1.00  inst_num_eq_res_simplified:             0
% 4.04/1.00  inst_num_child_elim:                    0
% 4.04/1.00  inst_num_of_dismatching_blockings:      100
% 4.04/1.00  inst_num_of_non_proper_insts:           721
% 4.04/1.00  inst_num_of_duplicates:                 0
% 4.04/1.00  inst_inst_num_from_inst_to_res:         0
% 4.04/1.00  inst_dismatching_checking_time:         0.
% 4.04/1.00  
% 4.04/1.00  ------ Resolution
% 4.04/1.00  
% 4.04/1.00  res_num_of_clauses:                     0
% 4.04/1.00  res_num_in_passive:                     0
% 4.04/1.00  res_num_in_active:                      0
% 4.04/1.00  res_num_of_loops:                       151
% 4.04/1.00  res_forward_subset_subsumed:            46
% 4.04/1.00  res_backward_subset_subsumed:           0
% 4.04/1.00  res_forward_subsumed:                   0
% 4.04/1.00  res_backward_subsumed:                  0
% 4.04/1.00  res_forward_subsumption_resolution:     0
% 4.04/1.00  res_backward_subsumption_resolution:    0
% 4.04/1.00  res_clause_to_clause_subsumption:       1207
% 4.04/1.00  res_orphan_elimination:                 0
% 4.04/1.00  res_tautology_del:                      49
% 4.04/1.00  res_num_eq_res_simplified:              0
% 4.04/1.00  res_num_sel_changes:                    0
% 4.04/1.00  res_moves_from_active_to_pass:          0
% 4.04/1.00  
% 4.04/1.00  ------ Superposition
% 4.04/1.00  
% 4.04/1.00  sup_time_total:                         0.
% 4.04/1.00  sup_time_generating:                    0.
% 4.04/1.00  sup_time_sim_full:                      0.
% 4.04/1.00  sup_time_sim_immed:                     0.
% 4.04/1.00  
% 4.04/1.00  sup_num_of_clauses:                     162
% 4.04/1.00  sup_num_in_active:                      103
% 4.04/1.00  sup_num_in_passive:                     59
% 4.04/1.00  sup_num_of_loops:                       105
% 4.04/1.00  sup_fw_superposition:                   190
% 4.04/1.00  sup_bw_superposition:                   14
% 4.04/1.00  sup_immediate_simplified:               70
% 4.04/1.00  sup_given_eliminated:                   0
% 4.04/1.00  comparisons_done:                       0
% 4.04/1.00  comparisons_avoided:                    0
% 4.04/1.00  
% 4.04/1.00  ------ Simplifications
% 4.04/1.00  
% 4.04/1.00  
% 4.04/1.00  sim_fw_subset_subsumed:                 2
% 4.04/1.00  sim_bw_subset_subsumed:                 0
% 4.04/1.00  sim_fw_subsumed:                        2
% 4.04/1.00  sim_bw_subsumed:                        0
% 4.04/1.00  sim_fw_subsumption_res:                 6
% 4.04/1.00  sim_bw_subsumption_res:                 0
% 4.04/1.00  sim_tautology_del:                      4
% 4.04/1.00  sim_eq_tautology_del:                   57
% 4.04/1.00  sim_eq_res_simp:                        3
% 4.04/1.00  sim_fw_demodulated:                     0
% 4.04/1.00  sim_bw_demodulated:                     3
% 4.04/1.00  sim_light_normalised:                   68
% 4.04/1.00  sim_joinable_taut:                      0
% 4.04/1.00  sim_joinable_simp:                      0
% 4.04/1.00  sim_ac_normalised:                      0
% 4.04/1.00  sim_smt_subsumption:                    0
% 4.04/1.00  
%------------------------------------------------------------------------------
