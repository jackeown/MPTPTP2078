%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:33 EST 2020

% Result     : Theorem 13.95s
% Output     : CNFRefutation 13.95s
% Verified   : 
% Statistics : Number of formulae       :  274 (6088 expanded)
%              Number of clauses        :  184 (1465 expanded)
%              Number of leaves         :   22 (2236 expanded)
%              Depth                    :   27
%              Number of atoms          : 1388 (71189 expanded)
%              Number of equality atoms :  583 (16458 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f38,f49,f48,f47,f46,f45,f44])).

fof(f81,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f77,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f59,f54])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f56,f54])).

fof(f87,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f85,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f52,f54])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(nnf_transformation,[],[f34])).

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

fof(f70,plain,(
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
    inference(equality_resolution,[],[f70])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f72,plain,(
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

fof(f73,plain,(
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

fof(f74,plain,(
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

fof(f75,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f88,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f50])).

fof(f69,plain,(
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
    inference(equality_resolution,[],[f69])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_262,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_30,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_549,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_30])).

cnf(c_550,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_34,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_32,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_552,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_550,c_34,c_32])).

cnf(c_578,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_262,c_552])).

cnf(c_579,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_927,plain,
    ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_579])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_939,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1448,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_939])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_15,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_460,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_15])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_15,c_11,c_10])).

cnf(c_465,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_607,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_12,c_465])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_15,c_12,c_11,c_10])).

cnf(c_612,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_611])).

cnf(c_925,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | v1_xboole_0(X2_55)
    | k1_relat_1(X0_55) = X1_55 ),
    inference(subtyping,[status(esa)],[c_612])).

cnf(c_1461,plain,
    ( k1_relat_1(X0_55) = X1_55
    | v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_925])).

cnf(c_8374,plain,
    ( k1_relat_1(sK4) = sK2
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_1461])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1842,plain,
    ( ~ v1_funct_2(sK4,X0_55,X1_55)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1_55)
    | k1_relat_1(sK4) = X0_55 ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_2029,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK4) = sK2 ),
    inference(instantiation,[status(thm)],[c_1842])).

cnf(c_8526,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8374,c_35,c_29,c_28,c_27,c_2029])).

cnf(c_949,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | v1_relat_1(X0_55) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1439,plain,
    ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | v1_relat_1(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_949])).

cnf(c_2270,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_1439])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_950,plain,
    ( ~ v1_relat_1(X0_55)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0_55),X1_55)) = k1_relat_1(k7_relat_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1438,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0_55),X1_55)) = k1_relat_1(k7_relat_1(X0_55,X1_55))
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_950])).

cnf(c_2380,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK4),X0_55)) = k1_relat_1(k7_relat_1(sK4,X0_55)) ),
    inference(superposition,[status(thm)],[c_2270,c_1438])).

cnf(c_8529,plain,
    ( k1_relat_1(k7_relat_1(sK4,X0_55)) = k1_setfam_1(k2_tarski(sK2,X0_55)) ),
    inference(demodulation,[status(thm)],[c_8526,c_2380])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_tarski(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_953,plain,
    ( ~ v1_relat_1(X0_55)
    | k7_relat_1(X0_55,k1_setfam_1(k2_tarski(k1_relat_1(X0_55),X1_55))) = k7_relat_1(X0_55,X1_55) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1437,plain,
    ( k7_relat_1(X0_55,k1_setfam_1(k2_tarski(k1_relat_1(X0_55),X1_55))) = k7_relat_1(X0_55,X1_55)
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_953])).

cnf(c_2391,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(k1_relat_1(sK4),X0_55))) = k7_relat_1(sK4,X0_55) ),
    inference(superposition,[status(thm)],[c_2270,c_1437])).

cnf(c_3303,plain,
    ( k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0_55))) = k7_relat_1(sK4,X0_55) ),
    inference(light_normalisation,[status(thm)],[c_2391,c_2380])).

cnf(c_10076,plain,
    ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,X0_55))) = k7_relat_1(sK4,X0_55) ),
    inference(demodulation,[status(thm)],[c_8529,c_3303])).

cnf(c_29208,plain,
    ( k7_relat_1(sK4,sK3) = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_927,c_10076])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_942,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1445,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_8373,plain,
    ( k1_relat_1(sK5) = sK3
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1461])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1837,plain,
    ( ~ v1_funct_2(sK5,X0_55,X1_55)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(X1_55)
    | k1_relat_1(sK5) = X0_55 ),
    inference(instantiation,[status(thm)],[c_925])).

cnf(c_2026,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | v1_xboole_0(sK1)
    | k1_relat_1(sK5) = sK3 ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_8518,plain,
    ( k1_relat_1(sK5) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8373,c_35,c_26,c_25,c_24,c_2026])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_583,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k1_relat_1(X0) != sK3
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_552])).

cnf(c_584,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,sK2) = k1_xboole_0
    | k1_relat_1(X0) != sK3 ),
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_926,plain,
    ( ~ v1_relat_1(X0_55)
    | k7_relat_1(X0_55,sK2) = k1_xboole_0
    | k1_relat_1(X0_55) != sK3 ),
    inference(subtyping,[status(esa)],[c_584])).

cnf(c_1460,plain,
    ( k7_relat_1(X0_55,sK2) = k1_xboole_0
    | k1_relat_1(X0_55) != sK3
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_926])).

cnf(c_8523,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8518,c_1460])).

cnf(c_1775,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_1936,plain,
    ( ~ v1_relat_1(sK5)
    | k7_relat_1(sK5,sK2) = k1_xboole_0
    | k1_relat_1(sK5) != sK3 ),
    inference(instantiation,[status(thm)],[c_926])).

cnf(c_10083,plain,
    ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8523,c_35,c_26,c_25,c_24,c_1775,c_1936,c_2026])).

cnf(c_2269,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1439])).

cnf(c_2379,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK5),X0_55)) = k1_relat_1(k7_relat_1(sK5,X0_55)) ),
    inference(superposition,[status(thm)],[c_2269,c_1438])).

cnf(c_8521,plain,
    ( k1_relat_1(k7_relat_1(sK5,X0_55)) = k1_setfam_1(k2_tarski(sK3,X0_55)) ),
    inference(demodulation,[status(thm)],[c_8518,c_2379])).

cnf(c_10086,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK2)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_10083,c_8521])).

cnf(c_6,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_951,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_10087,plain,
    ( k1_setfam_1(k2_tarski(sK3,sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10086,c_951])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_260,plain,
    ( r1_xboole_0(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_563,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k1_relat_1(X0) != X3
    | k1_setfam_1(k2_tarski(X2,X3)) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_260,c_3])).

cnf(c_564,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X1,k1_relat_1(X0))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_928,plain,
    ( ~ v1_relat_1(X0_55)
    | k7_relat_1(X0_55,X1_55) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X1_55,k1_relat_1(X0_55))) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_564])).

cnf(c_1459,plain,
    ( k7_relat_1(X0_55,X1_55) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X1_55,k1_relat_1(X0_55))) != k1_xboole_0
    | v1_relat_1(X0_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_928])).

cnf(c_25844,plain,
    ( k7_relat_1(sK4,X0_55) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0_55,sK2)) != k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_8526,c_1459])).

cnf(c_1778,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_949])).

cnf(c_25937,plain,
    ( ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,X0_55) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0_55,sK2)) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_25844])).

cnf(c_26276,plain,
    ( k1_setfam_1(k2_tarski(X0_55,sK2)) != k1_xboole_0
    | k7_relat_1(sK4,X0_55) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_25844,c_27,c_1778,c_25937])).

cnf(c_26277,plain,
    ( k7_relat_1(sK4,X0_55) = k1_xboole_0
    | k1_setfam_1(k2_tarski(X0_55,sK2)) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_26276])).

cnf(c_26281,plain,
    ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10087,c_26277])).

cnf(c_29214,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_29208,c_26281])).

cnf(c_2390,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(k1_relat_1(sK5),X0_55))) = k7_relat_1(sK5,X0_55) ),
    inference(superposition,[status(thm)],[c_2269,c_1437])).

cnf(c_3300,plain,
    ( k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0_55))) = k7_relat_1(sK5,X0_55) ),
    inference(light_normalisation,[status(thm)],[c_2390,c_2379])).

cnf(c_9773,plain,
    ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,X0_55))) = k7_relat_1(sK5,X0_55) ),
    inference(demodulation,[status(thm)],[c_8521,c_3300])).

cnf(c_27834,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2) ),
    inference(superposition,[status(thm)],[c_10087,c_9773])).

cnf(c_27840,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_27834,c_10083])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_936,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1451,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_936])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
    | k9_subset_1(X1_55,X2_55,X0_55) = k1_setfam_1(k2_tarski(X2_55,X0_55)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1436,plain,
    ( k9_subset_1(X0_55,X1_55,X2_55) = k1_setfam_1(k2_tarski(X1_55,X2_55))
    | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_2312,plain,
    ( k9_subset_1(sK0,X0_55,sK3) = k1_setfam_1(k2_tarski(X0_55,sK3)) ),
    inference(superposition,[status(thm)],[c_1451,c_1436])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_948,plain,
    ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1440,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_948])).

cnf(c_2451,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_1440])).

cnf(c_1852,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_55,X1_55,sK4,X2_55) = k7_relat_1(sK4,X2_55) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_2037,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
    inference(instantiation,[status(thm)],[c_1852])).

cnf(c_2702,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2451,c_29,c_27,c_2037])).

cnf(c_2450,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_1440])).

cnf(c_1847,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_55,X1_55,sK5,X2_55) = k7_relat_1(sK5,X2_55) ),
    inference(instantiation,[status(thm)],[c_948])).

cnf(c_2032,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_2697,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2450,c_26,c_24,c_2032])).

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
    inference(cnf_transformation,[],[f97])).

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
    inference(cnf_transformation,[],[f72])).

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
    inference(cnf_transformation,[],[f73])).

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
    inference(cnf_transformation,[],[f74])).

cnf(c_201,plain,
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

cnf(c_202,plain,
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
    inference(renaming,[status(thm)],[c_201])).

cnf(c_929,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55)
    | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
    | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X1_55) = X0_55 ),
    inference(subtyping,[status(esa)],[c_202])).

cnf(c_1458,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
    | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X0_55) = X2_55
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_929])).

cnf(c_6726,plain,
    ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),sK3) = sK5
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_1458])).

cnf(c_38,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_41,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_47,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_48,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_49,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20021,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),sK3) = sK5
    | k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6726,c_38,c_41,c_47,c_48,c_49])).

cnf(c_20022,plain,
    ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),sK3) = sK5
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_20021])).

cnf(c_20037,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2702,c_20022])).

cnf(c_39,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_44,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_45,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_46,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_20206,plain,
    ( v1_xboole_0(X0_55) = iProver_top
    | k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20037,c_39,c_44,c_45,c_46])).

cnf(c_20207,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_20206])).

cnf(c_20217,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_20207])).

cnf(c_20218,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20217,c_927])).

cnf(c_946,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1442,plain,
    ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
    | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55))) = iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X3_55) != iProver_top
    | v1_xboole_0(X5_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_946])).

cnf(c_3143,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
    | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
    | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_funct_1(X4_55) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55)) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(superposition,[status(thm)],[c_1442,c_1440])).

cnf(c_944,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55))
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1444,plain,
    ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
    | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
    | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
    | v1_funct_1(X0_55) != iProver_top
    | v1_funct_1(X3_55) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55)) = iProver_top
    | v1_xboole_0(X5_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_944])).

cnf(c_11002,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
    | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
    | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_funct_1(X4_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3143,c_1444])).

cnf(c_11006,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
    | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1445,c_11002])).

cnf(c_11113,plain,
    ( v1_funct_1(X2_55) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
    | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11006,c_38,c_41,c_47,c_48])).

cnf(c_11114,plain,
    ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
    | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_11113])).

cnf(c_11128,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_11114])).

cnf(c_11545,plain,
    ( v1_xboole_0(X0_55) = iProver_top
    | k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11128,c_39,c_44,c_45])).

cnf(c_11546,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_11545])).

cnf(c_11555,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1451,c_11546])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_37,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_11560,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11555,c_37,c_40])).

cnf(c_20219,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_20218,c_2312,c_11560])).

cnf(c_20220,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20219,c_927])).

cnf(c_23,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_943,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2504,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_2312,c_943])).

cnf(c_2505,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2504,c_927])).

cnf(c_2741,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2505,c_2697,c_2702])).

cnf(c_11564,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_11560,c_2741])).

cnf(c_11565,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_11564,c_11560])).

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
    inference(cnf_transformation,[],[f98])).

cnf(c_194,plain,
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

cnf(c_195,plain,
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
    inference(renaming,[status(thm)],[c_194])).

cnf(c_930,plain,
    ( ~ v1_funct_2(X0_55,X1_55,X2_55)
    | ~ v1_funct_2(X3_55,X4_55,X2_55)
    | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
    | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
    | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
    | ~ v1_funct_1(X0_55)
    | ~ v1_funct_1(X3_55)
    | v1_xboole_0(X2_55)
    | v1_xboole_0(X1_55)
    | v1_xboole_0(X4_55)
    | v1_xboole_0(X5_55)
    | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
    | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X4_55) = X3_55 ),
    inference(subtyping,[status(esa)],[c_195])).

cnf(c_1457,plain,
    ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
    | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X4_55) = X5_55
    | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
    | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
    | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
    | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
    | v1_funct_1(X2_55) != iProver_top
    | v1_funct_1(X5_55) != iProver_top
    | v1_xboole_0(X3_55) = iProver_top
    | v1_xboole_0(X1_55) = iProver_top
    | v1_xboole_0(X4_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_930])).

cnf(c_4581,plain,
    ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),X0_55) = X1_55
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_1457])).

cnf(c_8289,plain,
    ( v1_funct_1(X1_55) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),X0_55) = X1_55
    | k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(X2_55) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4581,c_38,c_41,c_47,c_48,c_49])).

cnf(c_8290,plain,
    ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
    | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),X0_55) = X1_55
    | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
    | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
    | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
    | v1_funct_1(X1_55) != iProver_top
    | v1_xboole_0(X2_55) = iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_8289])).

cnf(c_8305,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2702,c_8290])).

cnf(c_16559,plain,
    ( v1_xboole_0(X0_55) = iProver_top
    | k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8305,c_39,c_44,c_45,c_46])).

cnf(c_16560,plain,
    ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
    | v1_xboole_0(X0_55) = iProver_top ),
    inference(renaming,[status(thm)],[c_16559])).

cnf(c_16570,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2312,c_16560])).

cnf(c_16571,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16570,c_927])).

cnf(c_16572,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16571,c_2312,c_11560])).

cnf(c_16573,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16572,c_927])).

cnf(c_16574,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_16573])).

cnf(c_16576,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16573,c_36,c_33,c_31,c_16574])).

cnf(c_16577,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(renaming,[status(thm)],[c_16576])).

cnf(c_20221,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_20220])).

cnf(c_20223,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20220,c_36,c_33,c_31,c_11565,c_16577,c_20221])).

cnf(c_27846,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_27840,c_20223])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29214,c_27846])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:36:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 13.95/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.95/2.49  
% 13.95/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 13.95/2.49  
% 13.95/2.49  ------  iProver source info
% 13.95/2.49  
% 13.95/2.49  git: date: 2020-06-30 10:37:57 +0100
% 13.95/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 13.95/2.49  git: non_committed_changes: false
% 13.95/2.49  git: last_make_outside_of_git: false
% 13.95/2.49  
% 13.95/2.49  ------ 
% 13.95/2.49  
% 13.95/2.49  ------ Input Options
% 13.95/2.49  
% 13.95/2.49  --out_options                           all
% 13.95/2.49  --tptp_safe_out                         true
% 13.95/2.49  --problem_path                          ""
% 13.95/2.49  --include_path                          ""
% 13.95/2.49  --clausifier                            res/vclausify_rel
% 13.95/2.49  --clausifier_options                    --mode clausify
% 13.95/2.49  --stdin                                 false
% 13.95/2.49  --stats_out                             all
% 13.95/2.49  
% 13.95/2.49  ------ General Options
% 13.95/2.49  
% 13.95/2.49  --fof                                   false
% 13.95/2.49  --time_out_real                         305.
% 13.95/2.49  --time_out_virtual                      -1.
% 13.95/2.49  --symbol_type_check                     false
% 13.95/2.49  --clausify_out                          false
% 13.95/2.49  --sig_cnt_out                           false
% 13.95/2.49  --trig_cnt_out                          false
% 13.95/2.49  --trig_cnt_out_tolerance                1.
% 13.95/2.49  --trig_cnt_out_sk_spl                   false
% 13.95/2.49  --abstr_cl_out                          false
% 13.95/2.49  
% 13.95/2.49  ------ Global Options
% 13.95/2.49  
% 13.95/2.49  --schedule                              default
% 13.95/2.49  --add_important_lit                     false
% 13.95/2.49  --prop_solver_per_cl                    1000
% 13.95/2.49  --min_unsat_core                        false
% 13.95/2.49  --soft_assumptions                      false
% 13.95/2.49  --soft_lemma_size                       3
% 13.95/2.49  --prop_impl_unit_size                   0
% 13.95/2.49  --prop_impl_unit                        []
% 13.95/2.49  --share_sel_clauses                     true
% 13.95/2.49  --reset_solvers                         false
% 13.95/2.49  --bc_imp_inh                            [conj_cone]
% 13.95/2.49  --conj_cone_tolerance                   3.
% 13.95/2.49  --extra_neg_conj                        none
% 13.95/2.49  --large_theory_mode                     true
% 13.95/2.49  --prolific_symb_bound                   200
% 13.95/2.49  --lt_threshold                          2000
% 13.95/2.49  --clause_weak_htbl                      true
% 13.95/2.49  --gc_record_bc_elim                     false
% 13.95/2.49  
% 13.95/2.49  ------ Preprocessing Options
% 13.95/2.49  
% 13.95/2.49  --preprocessing_flag                    true
% 13.95/2.49  --time_out_prep_mult                    0.1
% 13.95/2.49  --splitting_mode                        input
% 13.95/2.49  --splitting_grd                         true
% 13.95/2.49  --splitting_cvd                         false
% 13.95/2.49  --splitting_cvd_svl                     false
% 13.95/2.49  --splitting_nvd                         32
% 13.95/2.49  --sub_typing                            true
% 13.95/2.49  --prep_gs_sim                           true
% 13.95/2.49  --prep_unflatten                        true
% 13.95/2.49  --prep_res_sim                          true
% 13.95/2.49  --prep_upred                            true
% 13.95/2.49  --prep_sem_filter                       exhaustive
% 13.95/2.49  --prep_sem_filter_out                   false
% 13.95/2.49  --pred_elim                             true
% 13.95/2.49  --res_sim_input                         true
% 13.95/2.49  --eq_ax_congr_red                       true
% 13.95/2.49  --pure_diseq_elim                       true
% 13.95/2.49  --brand_transform                       false
% 13.95/2.49  --non_eq_to_eq                          false
% 13.95/2.49  --prep_def_merge                        true
% 13.95/2.49  --prep_def_merge_prop_impl              false
% 13.95/2.49  --prep_def_merge_mbd                    true
% 13.95/2.49  --prep_def_merge_tr_red                 false
% 13.95/2.49  --prep_def_merge_tr_cl                  false
% 13.95/2.49  --smt_preprocessing                     true
% 13.95/2.49  --smt_ac_axioms                         fast
% 13.95/2.49  --preprocessed_out                      false
% 13.95/2.49  --preprocessed_stats                    false
% 13.95/2.49  
% 13.95/2.49  ------ Abstraction refinement Options
% 13.95/2.49  
% 13.95/2.49  --abstr_ref                             []
% 13.95/2.49  --abstr_ref_prep                        false
% 13.95/2.49  --abstr_ref_until_sat                   false
% 13.95/2.49  --abstr_ref_sig_restrict                funpre
% 13.95/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 13.95/2.49  --abstr_ref_under                       []
% 13.95/2.49  
% 13.95/2.49  ------ SAT Options
% 13.95/2.49  
% 13.95/2.49  --sat_mode                              false
% 13.95/2.49  --sat_fm_restart_options                ""
% 13.95/2.49  --sat_gr_def                            false
% 13.95/2.49  --sat_epr_types                         true
% 13.95/2.49  --sat_non_cyclic_types                  false
% 13.95/2.49  --sat_finite_models                     false
% 13.95/2.49  --sat_fm_lemmas                         false
% 13.95/2.49  --sat_fm_prep                           false
% 13.95/2.49  --sat_fm_uc_incr                        true
% 13.95/2.49  --sat_out_model                         small
% 13.95/2.49  --sat_out_clauses                       false
% 13.95/2.49  
% 13.95/2.49  ------ QBF Options
% 13.95/2.49  
% 13.95/2.49  --qbf_mode                              false
% 13.95/2.49  --qbf_elim_univ                         false
% 13.95/2.49  --qbf_dom_inst                          none
% 13.95/2.49  --qbf_dom_pre_inst                      false
% 13.95/2.49  --qbf_sk_in                             false
% 13.95/2.49  --qbf_pred_elim                         true
% 13.95/2.49  --qbf_split                             512
% 13.95/2.49  
% 13.95/2.49  ------ BMC1 Options
% 13.95/2.49  
% 13.95/2.49  --bmc1_incremental                      false
% 13.95/2.49  --bmc1_axioms                           reachable_all
% 13.95/2.49  --bmc1_min_bound                        0
% 13.95/2.49  --bmc1_max_bound                        -1
% 13.95/2.49  --bmc1_max_bound_default                -1
% 13.95/2.49  --bmc1_symbol_reachability              true
% 13.95/2.49  --bmc1_property_lemmas                  false
% 13.95/2.49  --bmc1_k_induction                      false
% 13.95/2.49  --bmc1_non_equiv_states                 false
% 13.95/2.49  --bmc1_deadlock                         false
% 13.95/2.49  --bmc1_ucm                              false
% 13.95/2.49  --bmc1_add_unsat_core                   none
% 13.95/2.49  --bmc1_unsat_core_children              false
% 13.95/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 13.95/2.49  --bmc1_out_stat                         full
% 13.95/2.49  --bmc1_ground_init                      false
% 13.95/2.49  --bmc1_pre_inst_next_state              false
% 13.95/2.49  --bmc1_pre_inst_state                   false
% 13.95/2.49  --bmc1_pre_inst_reach_state             false
% 13.95/2.49  --bmc1_out_unsat_core                   false
% 13.95/2.49  --bmc1_aig_witness_out                  false
% 13.95/2.49  --bmc1_verbose                          false
% 13.95/2.49  --bmc1_dump_clauses_tptp                false
% 13.95/2.49  --bmc1_dump_unsat_core_tptp             false
% 13.95/2.49  --bmc1_dump_file                        -
% 13.95/2.49  --bmc1_ucm_expand_uc_limit              128
% 13.95/2.49  --bmc1_ucm_n_expand_iterations          6
% 13.95/2.49  --bmc1_ucm_extend_mode                  1
% 13.95/2.49  --bmc1_ucm_init_mode                    2
% 13.95/2.49  --bmc1_ucm_cone_mode                    none
% 13.95/2.49  --bmc1_ucm_reduced_relation_type        0
% 13.95/2.49  --bmc1_ucm_relax_model                  4
% 13.95/2.49  --bmc1_ucm_full_tr_after_sat            true
% 13.95/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 13.95/2.49  --bmc1_ucm_layered_model                none
% 13.95/2.49  --bmc1_ucm_max_lemma_size               10
% 13.95/2.49  
% 13.95/2.49  ------ AIG Options
% 13.95/2.49  
% 13.95/2.49  --aig_mode                              false
% 13.95/2.49  
% 13.95/2.49  ------ Instantiation Options
% 13.95/2.49  
% 13.95/2.49  --instantiation_flag                    true
% 13.95/2.49  --inst_sos_flag                         false
% 13.95/2.49  --inst_sos_phase                        true
% 13.95/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 13.95/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 13.95/2.49  --inst_lit_sel_side                     num_symb
% 13.95/2.49  --inst_solver_per_active                1400
% 13.95/2.49  --inst_solver_calls_frac                1.
% 13.95/2.49  --inst_passive_queue_type               priority_queues
% 13.95/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 13.95/2.49  --inst_passive_queues_freq              [25;2]
% 13.95/2.49  --inst_dismatching                      true
% 13.95/2.49  --inst_eager_unprocessed_to_passive     true
% 13.95/2.49  --inst_prop_sim_given                   true
% 13.95/2.49  --inst_prop_sim_new                     false
% 13.95/2.49  --inst_subs_new                         false
% 13.95/2.49  --inst_eq_res_simp                      false
% 13.95/2.49  --inst_subs_given                       false
% 13.95/2.49  --inst_orphan_elimination               true
% 13.95/2.49  --inst_learning_loop_flag               true
% 13.95/2.49  --inst_learning_start                   3000
% 13.95/2.49  --inst_learning_factor                  2
% 13.95/2.49  --inst_start_prop_sim_after_learn       3
% 13.95/2.49  --inst_sel_renew                        solver
% 13.95/2.49  --inst_lit_activity_flag                true
% 13.95/2.49  --inst_restr_to_given                   false
% 13.95/2.49  --inst_activity_threshold               500
% 13.95/2.49  --inst_out_proof                        true
% 13.95/2.49  
% 13.95/2.49  ------ Resolution Options
% 13.95/2.49  
% 13.95/2.49  --resolution_flag                       true
% 13.95/2.49  --res_lit_sel                           adaptive
% 13.95/2.49  --res_lit_sel_side                      none
% 13.95/2.49  --res_ordering                          kbo
% 13.95/2.49  --res_to_prop_solver                    active
% 13.95/2.49  --res_prop_simpl_new                    false
% 13.95/2.49  --res_prop_simpl_given                  true
% 13.95/2.49  --res_passive_queue_type                priority_queues
% 13.95/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 13.95/2.49  --res_passive_queues_freq               [15;5]
% 13.95/2.49  --res_forward_subs                      full
% 13.95/2.49  --res_backward_subs                     full
% 13.95/2.49  --res_forward_subs_resolution           true
% 13.95/2.49  --res_backward_subs_resolution          true
% 13.95/2.49  --res_orphan_elimination                true
% 13.95/2.49  --res_time_limit                        2.
% 13.95/2.49  --res_out_proof                         true
% 13.95/2.49  
% 13.95/2.49  ------ Superposition Options
% 13.95/2.49  
% 13.95/2.49  --superposition_flag                    true
% 13.95/2.49  --sup_passive_queue_type                priority_queues
% 13.95/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 13.95/2.49  --sup_passive_queues_freq               [8;1;4]
% 13.95/2.49  --demod_completeness_check              fast
% 13.95/2.49  --demod_use_ground                      true
% 13.95/2.49  --sup_to_prop_solver                    passive
% 13.95/2.49  --sup_prop_simpl_new                    true
% 13.95/2.49  --sup_prop_simpl_given                  true
% 13.95/2.49  --sup_fun_splitting                     false
% 13.95/2.49  --sup_smt_interval                      50000
% 13.95/2.49  
% 13.95/2.49  ------ Superposition Simplification Setup
% 13.95/2.49  
% 13.95/2.49  --sup_indices_passive                   []
% 13.95/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 13.95/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 13.95/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 13.95/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 13.95/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 13.95/2.49  --sup_full_bw                           [BwDemod]
% 13.95/2.49  --sup_immed_triv                        [TrivRules]
% 13.95/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 13.95/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 13.95/2.49  --sup_immed_bw_main                     []
% 13.95/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 13.95/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 13.95/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 13.95/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 13.95/2.49  
% 13.95/2.49  ------ Combination Options
% 13.95/2.49  
% 13.95/2.49  --comb_res_mult                         3
% 13.95/2.49  --comb_sup_mult                         2
% 13.95/2.49  --comb_inst_mult                        10
% 13.95/2.49  
% 13.95/2.49  ------ Debug Options
% 13.95/2.49  
% 13.95/2.49  --dbg_backtrace                         false
% 13.95/2.49  --dbg_dump_prop_clauses                 false
% 13.95/2.49  --dbg_dump_prop_clauses_file            -
% 13.95/2.49  --dbg_out_stat                          false
% 13.95/2.49  ------ Parsing...
% 13.95/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 13.95/2.49  
% 13.95/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 13.95/2.49  
% 13.95/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 13.95/2.49  
% 13.95/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 13.95/2.49  ------ Proving...
% 13.95/2.49  ------ Problem Properties 
% 13.95/2.49  
% 13.95/2.49  
% 13.95/2.49  clauses                                 30
% 13.95/2.49  conjectures                             13
% 13.95/2.49  EPR                                     8
% 13.95/2.49  Horn                                    23
% 13.95/2.49  unary                                   15
% 13.95/2.49  binary                                  4
% 13.95/2.49  lits                                    124
% 13.95/2.49  lits eq                                 21
% 13.95/2.49  fd_pure                                 0
% 13.95/2.49  fd_pseudo                               0
% 13.95/2.49  fd_cond                                 0
% 13.95/2.49  fd_pseudo_cond                          1
% 13.95/2.49  AC symbols                              0
% 13.95/2.49  
% 13.95/2.49  ------ Schedule dynamic 5 is on 
% 13.95/2.49  
% 13.95/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 13.95/2.49  
% 13.95/2.49  
% 13.95/2.49  ------ 
% 13.95/2.49  Current options:
% 13.95/2.49  ------ 
% 13.95/2.49  
% 13.95/2.49  ------ Input Options
% 13.95/2.49  
% 13.95/2.49  --out_options                           all
% 13.95/2.49  --tptp_safe_out                         true
% 13.95/2.49  --problem_path                          ""
% 13.95/2.49  --include_path                          ""
% 13.95/2.49  --clausifier                            res/vclausify_rel
% 13.95/2.49  --clausifier_options                    --mode clausify
% 13.95/2.49  --stdin                                 false
% 13.95/2.49  --stats_out                             all
% 13.95/2.49  
% 13.95/2.49  ------ General Options
% 13.95/2.49  
% 13.95/2.49  --fof                                   false
% 13.95/2.49  --time_out_real                         305.
% 13.95/2.49  --time_out_virtual                      -1.
% 13.95/2.49  --symbol_type_check                     false
% 13.95/2.49  --clausify_out                          false
% 13.95/2.49  --sig_cnt_out                           false
% 13.95/2.49  --trig_cnt_out                          false
% 13.95/2.49  --trig_cnt_out_tolerance                1.
% 13.95/2.49  --trig_cnt_out_sk_spl                   false
% 13.95/2.49  --abstr_cl_out                          false
% 13.95/2.49  
% 13.95/2.49  ------ Global Options
% 13.95/2.49  
% 13.95/2.49  --schedule                              default
% 13.95/2.49  --add_important_lit                     false
% 13.95/2.49  --prop_solver_per_cl                    1000
% 13.95/2.49  --min_unsat_core                        false
% 13.95/2.49  --soft_assumptions                      false
% 13.95/2.49  --soft_lemma_size                       3
% 13.95/2.49  --prop_impl_unit_size                   0
% 13.95/2.49  --prop_impl_unit                        []
% 13.95/2.49  --share_sel_clauses                     true
% 13.95/2.49  --reset_solvers                         false
% 13.95/2.49  --bc_imp_inh                            [conj_cone]
% 13.95/2.49  --conj_cone_tolerance                   3.
% 13.95/2.49  --extra_neg_conj                        none
% 13.95/2.49  --large_theory_mode                     true
% 13.95/2.49  --prolific_symb_bound                   200
% 13.95/2.49  --lt_threshold                          2000
% 13.95/2.49  --clause_weak_htbl                      true
% 13.95/2.49  --gc_record_bc_elim                     false
% 13.95/2.49  
% 13.95/2.49  ------ Preprocessing Options
% 13.95/2.49  
% 13.95/2.49  --preprocessing_flag                    true
% 13.95/2.49  --time_out_prep_mult                    0.1
% 13.95/2.49  --splitting_mode                        input
% 13.95/2.49  --splitting_grd                         true
% 13.95/2.49  --splitting_cvd                         false
% 13.95/2.49  --splitting_cvd_svl                     false
% 13.95/2.49  --splitting_nvd                         32
% 13.95/2.49  --sub_typing                            true
% 13.95/2.49  --prep_gs_sim                           true
% 13.95/2.49  --prep_unflatten                        true
% 13.95/2.49  --prep_res_sim                          true
% 13.95/2.49  --prep_upred                            true
% 13.95/2.49  --prep_sem_filter                       exhaustive
% 13.95/2.49  --prep_sem_filter_out                   false
% 13.95/2.49  --pred_elim                             true
% 13.95/2.49  --res_sim_input                         true
% 13.95/2.49  --eq_ax_congr_red                       true
% 13.95/2.49  --pure_diseq_elim                       true
% 13.95/2.49  --brand_transform                       false
% 13.95/2.49  --non_eq_to_eq                          false
% 13.95/2.49  --prep_def_merge                        true
% 13.95/2.49  --prep_def_merge_prop_impl              false
% 13.95/2.49  --prep_def_merge_mbd                    true
% 13.95/2.49  --prep_def_merge_tr_red                 false
% 13.95/2.49  --prep_def_merge_tr_cl                  false
% 13.95/2.49  --smt_preprocessing                     true
% 13.95/2.49  --smt_ac_axioms                         fast
% 13.95/2.49  --preprocessed_out                      false
% 13.95/2.49  --preprocessed_stats                    false
% 13.95/2.49  
% 13.95/2.49  ------ Abstraction refinement Options
% 13.95/2.49  
% 13.95/2.49  --abstr_ref                             []
% 13.95/2.49  --abstr_ref_prep                        false
% 13.95/2.49  --abstr_ref_until_sat                   false
% 13.95/2.49  --abstr_ref_sig_restrict                funpre
% 13.95/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 13.95/2.49  --abstr_ref_under                       []
% 13.95/2.49  
% 13.95/2.49  ------ SAT Options
% 13.95/2.49  
% 13.95/2.49  --sat_mode                              false
% 13.95/2.49  --sat_fm_restart_options                ""
% 13.95/2.49  --sat_gr_def                            false
% 13.95/2.49  --sat_epr_types                         true
% 13.95/2.49  --sat_non_cyclic_types                  false
% 13.95/2.49  --sat_finite_models                     false
% 13.95/2.49  --sat_fm_lemmas                         false
% 13.95/2.49  --sat_fm_prep                           false
% 13.95/2.49  --sat_fm_uc_incr                        true
% 13.95/2.49  --sat_out_model                         small
% 13.95/2.49  --sat_out_clauses                       false
% 13.95/2.49  
% 13.95/2.49  ------ QBF Options
% 13.95/2.49  
% 13.95/2.49  --qbf_mode                              false
% 13.95/2.49  --qbf_elim_univ                         false
% 13.95/2.49  --qbf_dom_inst                          none
% 13.95/2.49  --qbf_dom_pre_inst                      false
% 13.95/2.49  --qbf_sk_in                             false
% 13.95/2.49  --qbf_pred_elim                         true
% 13.95/2.49  --qbf_split                             512
% 13.95/2.49  
% 13.95/2.49  ------ BMC1 Options
% 13.95/2.49  
% 13.95/2.49  --bmc1_incremental                      false
% 13.95/2.49  --bmc1_axioms                           reachable_all
% 13.95/2.49  --bmc1_min_bound                        0
% 13.95/2.49  --bmc1_max_bound                        -1
% 13.95/2.49  --bmc1_max_bound_default                -1
% 13.95/2.49  --bmc1_symbol_reachability              true
% 13.95/2.49  --bmc1_property_lemmas                  false
% 13.95/2.49  --bmc1_k_induction                      false
% 13.95/2.49  --bmc1_non_equiv_states                 false
% 13.95/2.49  --bmc1_deadlock                         false
% 13.95/2.49  --bmc1_ucm                              false
% 13.95/2.49  --bmc1_add_unsat_core                   none
% 13.95/2.49  --bmc1_unsat_core_children              false
% 13.95/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 13.95/2.49  --bmc1_out_stat                         full
% 13.95/2.49  --bmc1_ground_init                      false
% 13.95/2.49  --bmc1_pre_inst_next_state              false
% 13.95/2.49  --bmc1_pre_inst_state                   false
% 13.95/2.49  --bmc1_pre_inst_reach_state             false
% 13.95/2.49  --bmc1_out_unsat_core                   false
% 13.95/2.49  --bmc1_aig_witness_out                  false
% 13.95/2.49  --bmc1_verbose                          false
% 13.95/2.49  --bmc1_dump_clauses_tptp                false
% 13.95/2.49  --bmc1_dump_unsat_core_tptp             false
% 13.95/2.49  --bmc1_dump_file                        -
% 13.95/2.49  --bmc1_ucm_expand_uc_limit              128
% 13.95/2.49  --bmc1_ucm_n_expand_iterations          6
% 13.95/2.49  --bmc1_ucm_extend_mode                  1
% 13.95/2.49  --bmc1_ucm_init_mode                    2
% 13.95/2.49  --bmc1_ucm_cone_mode                    none
% 13.95/2.49  --bmc1_ucm_reduced_relation_type        0
% 13.95/2.49  --bmc1_ucm_relax_model                  4
% 13.95/2.49  --bmc1_ucm_full_tr_after_sat            true
% 13.95/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 13.95/2.49  --bmc1_ucm_layered_model                none
% 13.95/2.49  --bmc1_ucm_max_lemma_size               10
% 13.95/2.49  
% 13.95/2.49  ------ AIG Options
% 13.95/2.49  
% 13.95/2.49  --aig_mode                              false
% 13.95/2.49  
% 13.95/2.49  ------ Instantiation Options
% 13.95/2.49  
% 13.95/2.49  --instantiation_flag                    true
% 13.95/2.49  --inst_sos_flag                         false
% 13.95/2.49  --inst_sos_phase                        true
% 13.95/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 13.95/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 13.95/2.49  --inst_lit_sel_side                     none
% 13.95/2.49  --inst_solver_per_active                1400
% 13.95/2.49  --inst_solver_calls_frac                1.
% 13.95/2.49  --inst_passive_queue_type               priority_queues
% 13.95/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 13.95/2.49  --inst_passive_queues_freq              [25;2]
% 13.95/2.49  --inst_dismatching                      true
% 13.95/2.49  --inst_eager_unprocessed_to_passive     true
% 13.95/2.49  --inst_prop_sim_given                   true
% 13.95/2.49  --inst_prop_sim_new                     false
% 13.95/2.49  --inst_subs_new                         false
% 13.95/2.49  --inst_eq_res_simp                      false
% 13.95/2.49  --inst_subs_given                       false
% 13.95/2.49  --inst_orphan_elimination               true
% 13.95/2.49  --inst_learning_loop_flag               true
% 13.95/2.49  --inst_learning_start                   3000
% 13.95/2.49  --inst_learning_factor                  2
% 13.95/2.49  --inst_start_prop_sim_after_learn       3
% 13.95/2.49  --inst_sel_renew                        solver
% 13.95/2.49  --inst_lit_activity_flag                true
% 13.95/2.49  --inst_restr_to_given                   false
% 13.95/2.49  --inst_activity_threshold               500
% 13.95/2.49  --inst_out_proof                        true
% 13.95/2.49  
% 13.95/2.49  ------ Resolution Options
% 13.95/2.49  
% 13.95/2.49  --resolution_flag                       false
% 13.95/2.49  --res_lit_sel                           adaptive
% 13.95/2.49  --res_lit_sel_side                      none
% 13.95/2.49  --res_ordering                          kbo
% 13.95/2.49  --res_to_prop_solver                    active
% 13.95/2.49  --res_prop_simpl_new                    false
% 13.95/2.49  --res_prop_simpl_given                  true
% 13.95/2.49  --res_passive_queue_type                priority_queues
% 13.95/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 13.95/2.49  --res_passive_queues_freq               [15;5]
% 13.95/2.49  --res_forward_subs                      full
% 13.95/2.49  --res_backward_subs                     full
% 13.95/2.49  --res_forward_subs_resolution           true
% 13.95/2.49  --res_backward_subs_resolution          true
% 13.95/2.49  --res_orphan_elimination                true
% 13.95/2.49  --res_time_limit                        2.
% 13.95/2.49  --res_out_proof                         true
% 13.95/2.49  
% 13.95/2.49  ------ Superposition Options
% 13.95/2.49  
% 13.95/2.49  --superposition_flag                    true
% 13.95/2.49  --sup_passive_queue_type                priority_queues
% 13.95/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 13.95/2.49  --sup_passive_queues_freq               [8;1;4]
% 13.95/2.49  --demod_completeness_check              fast
% 13.95/2.49  --demod_use_ground                      true
% 13.95/2.49  --sup_to_prop_solver                    passive
% 13.95/2.49  --sup_prop_simpl_new                    true
% 13.95/2.49  --sup_prop_simpl_given                  true
% 13.95/2.49  --sup_fun_splitting                     false
% 13.95/2.49  --sup_smt_interval                      50000
% 13.95/2.49  
% 13.95/2.49  ------ Superposition Simplification Setup
% 13.95/2.49  
% 13.95/2.49  --sup_indices_passive                   []
% 13.95/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 13.95/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 13.95/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 13.95/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 13.95/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 13.95/2.49  --sup_full_bw                           [BwDemod]
% 13.95/2.49  --sup_immed_triv                        [TrivRules]
% 13.95/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 13.95/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 13.95/2.49  --sup_immed_bw_main                     []
% 13.95/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 13.95/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 13.95/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 13.95/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 13.95/2.49  
% 13.95/2.49  ------ Combination Options
% 13.95/2.49  
% 13.95/2.49  --comb_res_mult                         3
% 13.95/2.49  --comb_sup_mult                         2
% 13.95/2.49  --comb_inst_mult                        10
% 13.95/2.49  
% 13.95/2.49  ------ Debug Options
% 13.95/2.49  
% 13.95/2.49  --dbg_backtrace                         false
% 13.95/2.49  --dbg_dump_prop_clauses                 false
% 13.95/2.49  --dbg_dump_prop_clauses_file            -
% 13.95/2.49  --dbg_out_stat                          false
% 13.95/2.49  
% 13.95/2.49  
% 13.95/2.49  
% 13.95/2.49  
% 13.95/2.49  ------ Proving...
% 13.95/2.49  
% 13.95/2.49  
% 13.95/2.49  % SZS status Theorem for theBenchmark.p
% 13.95/2.49  
% 13.95/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 13.95/2.49  
% 13.95/2.49  fof(f1,axiom,(
% 13.95/2.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f39,plain,(
% 13.95/2.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 13.95/2.49    inference(nnf_transformation,[],[f1])).
% 13.95/2.49  
% 13.95/2.49  fof(f51,plain,(
% 13.95/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f39])).
% 13.95/2.49  
% 13.95/2.49  fof(f3,axiom,(
% 13.95/2.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f54,plain,(
% 13.95/2.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 13.95/2.49    inference(cnf_transformation,[],[f3])).
% 13.95/2.49  
% 13.95/2.49  fof(f90,plain,(
% 13.95/2.49    ( ! [X0,X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 13.95/2.49    inference(definition_unfolding,[],[f51,f54])).
% 13.95/2.49  
% 13.95/2.49  fof(f8,axiom,(
% 13.95/2.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f23,plain,(
% 13.95/2.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 13.95/2.49    inference(ennf_transformation,[],[f8])).
% 13.95/2.49  
% 13.95/2.49  fof(f24,plain,(
% 13.95/2.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 13.95/2.49    inference(flattening,[],[f23])).
% 13.95/2.49  
% 13.95/2.49  fof(f40,plain,(
% 13.95/2.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 13.95/2.49    inference(nnf_transformation,[],[f24])).
% 13.95/2.49  
% 13.95/2.49  fof(f60,plain,(
% 13.95/2.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f40])).
% 13.95/2.49  
% 13.95/2.49  fof(f16,conjecture,(
% 13.95/2.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f17,negated_conjecture,(
% 13.95/2.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 13.95/2.49    inference(negated_conjecture,[],[f16])).
% 13.95/2.49  
% 13.95/2.49  fof(f37,plain,(
% 13.95/2.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 13.95/2.49    inference(ennf_transformation,[],[f17])).
% 13.95/2.49  
% 13.95/2.49  fof(f38,plain,(
% 13.95/2.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 13.95/2.49    inference(flattening,[],[f37])).
% 13.95/2.49  
% 13.95/2.49  fof(f49,plain,(
% 13.95/2.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 13.95/2.49    introduced(choice_axiom,[])).
% 13.95/2.49  
% 13.95/2.49  fof(f48,plain,(
% 13.95/2.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 13.95/2.49    introduced(choice_axiom,[])).
% 13.95/2.49  
% 13.95/2.49  fof(f47,plain,(
% 13.95/2.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 13.95/2.49    introduced(choice_axiom,[])).
% 13.95/2.49  
% 13.95/2.49  fof(f46,plain,(
% 13.95/2.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 13.95/2.49    introduced(choice_axiom,[])).
% 13.95/2.49  
% 13.95/2.49  fof(f45,plain,(
% 13.95/2.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 13.95/2.49    introduced(choice_axiom,[])).
% 13.95/2.49  
% 13.95/2.49  fof(f44,plain,(
% 13.95/2.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 13.95/2.49    introduced(choice_axiom,[])).
% 13.95/2.49  
% 13.95/2.49  fof(f50,plain,(
% 13.95/2.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 13.95/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f38,f49,f48,f47,f46,f45,f44])).
% 13.95/2.49  
% 13.95/2.49  fof(f81,plain,(
% 13.95/2.49    r1_subset_1(sK2,sK3)),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f77,plain,(
% 13.95/2.49    ~v1_xboole_0(sK2)),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f79,plain,(
% 13.95/2.49    ~v1_xboole_0(sK3)),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f84,plain,(
% 13.95/2.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f11,axiom,(
% 13.95/2.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f27,plain,(
% 13.95/2.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 13.95/2.49    inference(ennf_transformation,[],[f11])).
% 13.95/2.49  
% 13.95/2.49  fof(f28,plain,(
% 13.95/2.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 13.95/2.49    inference(flattening,[],[f27])).
% 13.95/2.49  
% 13.95/2.49  fof(f65,plain,(
% 13.95/2.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f28])).
% 13.95/2.49  
% 13.95/2.49  fof(f10,axiom,(
% 13.95/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f18,plain,(
% 13.95/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 13.95/2.49    inference(pure_predicate_removal,[],[f10])).
% 13.95/2.49  
% 13.95/2.49  fof(f26,plain,(
% 13.95/2.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 13.95/2.49    inference(ennf_transformation,[],[f18])).
% 13.95/2.49  
% 13.95/2.49  fof(f63,plain,(
% 13.95/2.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.95/2.49    inference(cnf_transformation,[],[f26])).
% 13.95/2.49  
% 13.95/2.49  fof(f12,axiom,(
% 13.95/2.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f29,plain,(
% 13.95/2.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 13.95/2.49    inference(ennf_transformation,[],[f12])).
% 13.95/2.49  
% 13.95/2.49  fof(f30,plain,(
% 13.95/2.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 13.95/2.49    inference(flattening,[],[f29])).
% 13.95/2.49  
% 13.95/2.49  fof(f41,plain,(
% 13.95/2.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 13.95/2.49    inference(nnf_transformation,[],[f30])).
% 13.95/2.49  
% 13.95/2.49  fof(f66,plain,(
% 13.95/2.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f41])).
% 13.95/2.49  
% 13.95/2.49  fof(f9,axiom,(
% 13.95/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f25,plain,(
% 13.95/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 13.95/2.49    inference(ennf_transformation,[],[f9])).
% 13.95/2.49  
% 13.95/2.49  fof(f62,plain,(
% 13.95/2.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 13.95/2.49    inference(cnf_transformation,[],[f25])).
% 13.95/2.49  
% 13.95/2.49  fof(f76,plain,(
% 13.95/2.49    ~v1_xboole_0(sK1)),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f82,plain,(
% 13.95/2.49    v1_funct_1(sK4)),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f83,plain,(
% 13.95/2.49    v1_funct_2(sK4,sK2,sK1)),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f7,axiom,(
% 13.95/2.49    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f22,plain,(
% 13.95/2.49    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 13.95/2.49    inference(ennf_transformation,[],[f7])).
% 13.95/2.49  
% 13.95/2.49  fof(f59,plain,(
% 13.95/2.49    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f22])).
% 13.95/2.49  
% 13.95/2.49  fof(f93,plain,(
% 13.95/2.49    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 13.95/2.49    inference(definition_unfolding,[],[f59,f54])).
% 13.95/2.49  
% 13.95/2.49  fof(f5,axiom,(
% 13.95/2.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f21,plain,(
% 13.95/2.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 13.95/2.49    inference(ennf_transformation,[],[f5])).
% 13.95/2.49  
% 13.95/2.49  fof(f56,plain,(
% 13.95/2.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f21])).
% 13.95/2.49  
% 13.95/2.49  fof(f92,plain,(
% 13.95/2.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k1_setfam_1(k2_tarski(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 13.95/2.49    inference(definition_unfolding,[],[f56,f54])).
% 13.95/2.49  
% 13.95/2.49  fof(f87,plain,(
% 13.95/2.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f85,plain,(
% 13.95/2.49    v1_funct_1(sK5)),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f86,plain,(
% 13.95/2.49    v1_funct_2(sK5,sK3,sK1)),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f4,axiom,(
% 13.95/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f20,plain,(
% 13.95/2.49    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 13.95/2.49    inference(ennf_transformation,[],[f4])).
% 13.95/2.49  
% 13.95/2.49  fof(f55,plain,(
% 13.95/2.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f20])).
% 13.95/2.49  
% 13.95/2.49  fof(f6,axiom,(
% 13.95/2.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f57,plain,(
% 13.95/2.49    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 13.95/2.49    inference(cnf_transformation,[],[f6])).
% 13.95/2.49  
% 13.95/2.49  fof(f52,plain,(
% 13.95/2.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 13.95/2.49    inference(cnf_transformation,[],[f39])).
% 13.95/2.49  
% 13.95/2.49  fof(f89,plain,(
% 13.95/2.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 13.95/2.49    inference(definition_unfolding,[],[f52,f54])).
% 13.95/2.49  
% 13.95/2.49  fof(f80,plain,(
% 13.95/2.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f2,axiom,(
% 13.95/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f19,plain,(
% 13.95/2.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 13.95/2.49    inference(ennf_transformation,[],[f2])).
% 13.95/2.49  
% 13.95/2.49  fof(f53,plain,(
% 13.95/2.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 13.95/2.49    inference(cnf_transformation,[],[f19])).
% 13.95/2.49  
% 13.95/2.49  fof(f91,plain,(
% 13.95/2.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 13.95/2.49    inference(definition_unfolding,[],[f53,f54])).
% 13.95/2.49  
% 13.95/2.49  fof(f13,axiom,(
% 13.95/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f31,plain,(
% 13.95/2.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 13.95/2.49    inference(ennf_transformation,[],[f13])).
% 13.95/2.49  
% 13.95/2.49  fof(f32,plain,(
% 13.95/2.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 13.95/2.49    inference(flattening,[],[f31])).
% 13.95/2.49  
% 13.95/2.49  fof(f68,plain,(
% 13.95/2.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f32])).
% 13.95/2.49  
% 13.95/2.49  fof(f14,axiom,(
% 13.95/2.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f33,plain,(
% 13.95/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 13.95/2.49    inference(ennf_transformation,[],[f14])).
% 13.95/2.49  
% 13.95/2.49  fof(f34,plain,(
% 13.95/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 13.95/2.49    inference(flattening,[],[f33])).
% 13.95/2.49  
% 13.95/2.49  fof(f42,plain,(
% 13.95/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 13.95/2.49    inference(nnf_transformation,[],[f34])).
% 13.95/2.49  
% 13.95/2.49  fof(f43,plain,(
% 13.95/2.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 13.95/2.49    inference(flattening,[],[f42])).
% 13.95/2.49  
% 13.95/2.49  fof(f70,plain,(
% 13.95/2.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f43])).
% 13.95/2.49  
% 13.95/2.49  fof(f97,plain,(
% 13.95/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 13.95/2.49    inference(equality_resolution,[],[f70])).
% 13.95/2.49  
% 13.95/2.49  fof(f15,axiom,(
% 13.95/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 13.95/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 13.95/2.49  
% 13.95/2.49  fof(f35,plain,(
% 13.95/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 13.95/2.49    inference(ennf_transformation,[],[f15])).
% 13.95/2.49  
% 13.95/2.49  fof(f36,plain,(
% 13.95/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 13.95/2.49    inference(flattening,[],[f35])).
% 13.95/2.49  
% 13.95/2.49  fof(f72,plain,(
% 13.95/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f36])).
% 13.95/2.49  
% 13.95/2.49  fof(f73,plain,(
% 13.95/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f36])).
% 13.95/2.49  
% 13.95/2.49  fof(f74,plain,(
% 13.95/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f36])).
% 13.95/2.49  
% 13.95/2.49  fof(f75,plain,(
% 13.95/2.49    ~v1_xboole_0(sK0)),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f78,plain,(
% 13.95/2.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f88,plain,(
% 13.95/2.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 13.95/2.49    inference(cnf_transformation,[],[f50])).
% 13.95/2.49  
% 13.95/2.49  fof(f69,plain,(
% 13.95/2.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 13.95/2.49    inference(cnf_transformation,[],[f43])).
% 13.95/2.49  
% 13.95/2.49  fof(f98,plain,(
% 13.95/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 13.95/2.49    inference(equality_resolution,[],[f69])).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1,plain,
% 13.95/2.49      ( ~ r1_xboole_0(X0,X1)
% 13.95/2.49      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 13.95/2.49      inference(cnf_transformation,[],[f90]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_262,plain,
% 13.95/2.49      ( ~ r1_xboole_0(X0,X1)
% 13.95/2.49      | k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0 ),
% 13.95/2.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_9,plain,
% 13.95/2.49      ( ~ r1_subset_1(X0,X1)
% 13.95/2.49      | r1_xboole_0(X0,X1)
% 13.95/2.49      | v1_xboole_0(X0)
% 13.95/2.49      | v1_xboole_0(X1) ),
% 13.95/2.49      inference(cnf_transformation,[],[f60]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_30,negated_conjecture,
% 13.95/2.49      ( r1_subset_1(sK2,sK3) ),
% 13.95/2.49      inference(cnf_transformation,[],[f81]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_549,plain,
% 13.95/2.49      ( r1_xboole_0(X0,X1)
% 13.95/2.49      | v1_xboole_0(X0)
% 13.95/2.49      | v1_xboole_0(X1)
% 13.95/2.49      | sK3 != X1
% 13.95/2.49      | sK2 != X0 ),
% 13.95/2.49      inference(resolution_lifted,[status(thm)],[c_9,c_30]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_550,plain,
% 13.95/2.49      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 13.95/2.49      inference(unflattening,[status(thm)],[c_549]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_34,negated_conjecture,
% 13.95/2.49      ( ~ v1_xboole_0(sK2) ),
% 13.95/2.49      inference(cnf_transformation,[],[f77]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_32,negated_conjecture,
% 13.95/2.49      ( ~ v1_xboole_0(sK3) ),
% 13.95/2.49      inference(cnf_transformation,[],[f79]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_552,plain,
% 13.95/2.49      ( r1_xboole_0(sK2,sK3) ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_550,c_34,c_32]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_578,plain,
% 13.95/2.49      ( k1_setfam_1(k2_tarski(X0,X1)) = k1_xboole_0
% 13.95/2.49      | sK3 != X1
% 13.95/2.49      | sK2 != X0 ),
% 13.95/2.49      inference(resolution_lifted,[status(thm)],[c_262,c_552]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_579,plain,
% 13.95/2.49      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 13.95/2.49      inference(unflattening,[status(thm)],[c_578]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_927,plain,
% 13.95/2.49      ( k1_setfam_1(k2_tarski(sK2,sK3)) = k1_xboole_0 ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_579]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_27,negated_conjecture,
% 13.95/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 13.95/2.49      inference(cnf_transformation,[],[f84]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_939,negated_conjecture,
% 13.95/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_27]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1448,plain,
% 13.95/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_939]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_12,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | v1_partfun1(X0,X1)
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | v1_xboole_0(X2) ),
% 13.95/2.49      inference(cnf_transformation,[],[f65]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11,plain,
% 13.95/2.49      ( v4_relat_1(X0,X1)
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 13.95/2.49      inference(cnf_transformation,[],[f63]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_15,plain,
% 13.95/2.49      ( ~ v1_partfun1(X0,X1)
% 13.95/2.49      | ~ v4_relat_1(X0,X1)
% 13.95/2.49      | ~ v1_relat_1(X0)
% 13.95/2.49      | k1_relat_1(X0) = X1 ),
% 13.95/2.49      inference(cnf_transformation,[],[f66]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_460,plain,
% 13.95/2.49      ( ~ v1_partfun1(X0,X1)
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ v1_relat_1(X0)
% 13.95/2.49      | k1_relat_1(X0) = X1 ),
% 13.95/2.49      inference(resolution,[status(thm)],[c_11,c_15]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_10,plain,
% 13.95/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | v1_relat_1(X0) ),
% 13.95/2.49      inference(cnf_transformation,[],[f62]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_464,plain,
% 13.95/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ v1_partfun1(X0,X1)
% 13.95/2.49      | k1_relat_1(X0) = X1 ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_460,c_15,c_11,c_10]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_465,plain,
% 13.95/2.49      ( ~ v1_partfun1(X0,X1)
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | k1_relat_1(X0) = X1 ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_464]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_607,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | k1_relat_1(X0) = X1 ),
% 13.95/2.49      inference(resolution,[status(thm)],[c_12,c_465]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_611,plain,
% 13.95/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | k1_relat_1(X0) = X1 ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_607,c_15,c_12,c_11,c_10]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_612,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | k1_relat_1(X0) = X1 ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_611]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_925,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 13.95/2.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 13.95/2.49      | ~ v1_funct_1(X0_55)
% 13.95/2.49      | v1_xboole_0(X2_55)
% 13.95/2.49      | k1_relat_1(X0_55) = X1_55 ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_612]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1461,plain,
% 13.95/2.49      ( k1_relat_1(X0_55) = X1_55
% 13.95/2.49      | v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 13.95/2.49      | v1_funct_1(X0_55) != iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_925]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_8374,plain,
% 13.95/2.49      ( k1_relat_1(sK4) = sK2
% 13.95/2.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 13.95/2.49      | v1_funct_1(sK4) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK1) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1448,c_1461]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_35,negated_conjecture,
% 13.95/2.49      ( ~ v1_xboole_0(sK1) ),
% 13.95/2.49      inference(cnf_transformation,[],[f76]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_29,negated_conjecture,
% 13.95/2.49      ( v1_funct_1(sK4) ),
% 13.95/2.49      inference(cnf_transformation,[],[f82]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_28,negated_conjecture,
% 13.95/2.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 13.95/2.49      inference(cnf_transformation,[],[f83]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1842,plain,
% 13.95/2.49      ( ~ v1_funct_2(sK4,X0_55,X1_55)
% 13.95/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 13.95/2.49      | ~ v1_funct_1(sK4)
% 13.95/2.49      | v1_xboole_0(X1_55)
% 13.95/2.49      | k1_relat_1(sK4) = X0_55 ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_925]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2029,plain,
% 13.95/2.49      ( ~ v1_funct_2(sK4,sK2,sK1)
% 13.95/2.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 13.95/2.49      | ~ v1_funct_1(sK4)
% 13.95/2.49      | v1_xboole_0(sK1)
% 13.95/2.49      | k1_relat_1(sK4) = sK2 ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_1842]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_8526,plain,
% 13.95/2.49      ( k1_relat_1(sK4) = sK2 ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_8374,c_35,c_29,c_28,c_27,c_2029]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_949,plain,
% 13.95/2.49      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 13.95/2.49      | v1_relat_1(X0_55) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_10]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1439,plain,
% 13.95/2.49      ( m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 13.95/2.49      | v1_relat_1(X0_55) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_949]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2270,plain,
% 13.95/2.49      ( v1_relat_1(sK4) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1448,c_1439]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_7,plain,
% 13.95/2.49      ( ~ v1_relat_1(X0)
% 13.95/2.49      | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 13.95/2.49      inference(cnf_transformation,[],[f93]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_950,plain,
% 13.95/2.49      ( ~ v1_relat_1(X0_55)
% 13.95/2.49      | k1_setfam_1(k2_tarski(k1_relat_1(X0_55),X1_55)) = k1_relat_1(k7_relat_1(X0_55,X1_55)) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_7]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1438,plain,
% 13.95/2.49      ( k1_setfam_1(k2_tarski(k1_relat_1(X0_55),X1_55)) = k1_relat_1(k7_relat_1(X0_55,X1_55))
% 13.95/2.49      | v1_relat_1(X0_55) != iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_950]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2380,plain,
% 13.95/2.49      ( k1_setfam_1(k2_tarski(k1_relat_1(sK4),X0_55)) = k1_relat_1(k7_relat_1(sK4,X0_55)) ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_2270,c_1438]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_8529,plain,
% 13.95/2.49      ( k1_relat_1(k7_relat_1(sK4,X0_55)) = k1_setfam_1(k2_tarski(sK2,X0_55)) ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_8526,c_2380]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_4,plain,
% 13.95/2.49      ( ~ v1_relat_1(X0)
% 13.95/2.49      | k7_relat_1(X0,k1_setfam_1(k2_tarski(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
% 13.95/2.49      inference(cnf_transformation,[],[f92]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_953,plain,
% 13.95/2.49      ( ~ v1_relat_1(X0_55)
% 13.95/2.49      | k7_relat_1(X0_55,k1_setfam_1(k2_tarski(k1_relat_1(X0_55),X1_55))) = k7_relat_1(X0_55,X1_55) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_4]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1437,plain,
% 13.95/2.49      ( k7_relat_1(X0_55,k1_setfam_1(k2_tarski(k1_relat_1(X0_55),X1_55))) = k7_relat_1(X0_55,X1_55)
% 13.95/2.49      | v1_relat_1(X0_55) != iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_953]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2391,plain,
% 13.95/2.49      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(k1_relat_1(sK4),X0_55))) = k7_relat_1(sK4,X0_55) ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_2270,c_1437]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_3303,plain,
% 13.95/2.49      ( k7_relat_1(sK4,k1_relat_1(k7_relat_1(sK4,X0_55))) = k7_relat_1(sK4,X0_55) ),
% 13.95/2.49      inference(light_normalisation,[status(thm)],[c_2391,c_2380]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_10076,plain,
% 13.95/2.49      ( k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,X0_55))) = k7_relat_1(sK4,X0_55) ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_8529,c_3303]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_29208,plain,
% 13.95/2.49      ( k7_relat_1(sK4,sK3) = k7_relat_1(sK4,k1_xboole_0) ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_927,c_10076]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_24,negated_conjecture,
% 13.95/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 13.95/2.49      inference(cnf_transformation,[],[f87]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_942,negated_conjecture,
% 13.95/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_24]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1445,plain,
% 13.95/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_942]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_8373,plain,
% 13.95/2.49      ( k1_relat_1(sK5) = sK3
% 13.95/2.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 13.95/2.49      | v1_funct_1(sK5) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK1) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1445,c_1461]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_26,negated_conjecture,
% 13.95/2.49      ( v1_funct_1(sK5) ),
% 13.95/2.49      inference(cnf_transformation,[],[f85]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_25,negated_conjecture,
% 13.95/2.49      ( v1_funct_2(sK5,sK3,sK1) ),
% 13.95/2.49      inference(cnf_transformation,[],[f86]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1837,plain,
% 13.95/2.49      ( ~ v1_funct_2(sK5,X0_55,X1_55)
% 13.95/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 13.95/2.49      | ~ v1_funct_1(sK5)
% 13.95/2.49      | v1_xboole_0(X1_55)
% 13.95/2.49      | k1_relat_1(sK5) = X0_55 ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_925]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2026,plain,
% 13.95/2.49      ( ~ v1_funct_2(sK5,sK3,sK1)
% 13.95/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 13.95/2.49      | ~ v1_funct_1(sK5)
% 13.95/2.49      | v1_xboole_0(sK1)
% 13.95/2.49      | k1_relat_1(sK5) = sK3 ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_1837]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_8518,plain,
% 13.95/2.49      ( k1_relat_1(sK5) = sK3 ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_8373,c_35,c_26,c_25,c_24,c_2026]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_3,plain,
% 13.95/2.49      ( ~ r1_xboole_0(X0,k1_relat_1(X1))
% 13.95/2.49      | ~ v1_relat_1(X1)
% 13.95/2.49      | k7_relat_1(X1,X0) = k1_xboole_0 ),
% 13.95/2.49      inference(cnf_transformation,[],[f55]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_583,plain,
% 13.95/2.49      ( ~ v1_relat_1(X0)
% 13.95/2.49      | k7_relat_1(X0,X1) = k1_xboole_0
% 13.95/2.49      | k1_relat_1(X0) != sK3
% 13.95/2.49      | sK2 != X1 ),
% 13.95/2.49      inference(resolution_lifted,[status(thm)],[c_3,c_552]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_584,plain,
% 13.95/2.49      ( ~ v1_relat_1(X0)
% 13.95/2.49      | k7_relat_1(X0,sK2) = k1_xboole_0
% 13.95/2.49      | k1_relat_1(X0) != sK3 ),
% 13.95/2.49      inference(unflattening,[status(thm)],[c_583]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_926,plain,
% 13.95/2.49      ( ~ v1_relat_1(X0_55)
% 13.95/2.49      | k7_relat_1(X0_55,sK2) = k1_xboole_0
% 13.95/2.49      | k1_relat_1(X0_55) != sK3 ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_584]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1460,plain,
% 13.95/2.49      ( k7_relat_1(X0_55,sK2) = k1_xboole_0
% 13.95/2.49      | k1_relat_1(X0_55) != sK3
% 13.95/2.49      | v1_relat_1(X0_55) != iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_926]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_8523,plain,
% 13.95/2.49      ( k7_relat_1(sK5,sK2) = k1_xboole_0
% 13.95/2.49      | v1_relat_1(sK5) != iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_8518,c_1460]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1775,plain,
% 13.95/2.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 13.95/2.49      | v1_relat_1(sK5) ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_949]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1936,plain,
% 13.95/2.49      ( ~ v1_relat_1(sK5)
% 13.95/2.49      | k7_relat_1(sK5,sK2) = k1_xboole_0
% 13.95/2.49      | k1_relat_1(sK5) != sK3 ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_926]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_10083,plain,
% 13.95/2.49      ( k7_relat_1(sK5,sK2) = k1_xboole_0 ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_8523,c_35,c_26,c_25,c_24,c_1775,c_1936,c_2026]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2269,plain,
% 13.95/2.49      ( v1_relat_1(sK5) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1445,c_1439]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2379,plain,
% 13.95/2.49      ( k1_setfam_1(k2_tarski(k1_relat_1(sK5),X0_55)) = k1_relat_1(k7_relat_1(sK5,X0_55)) ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_2269,c_1438]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_8521,plain,
% 13.95/2.49      ( k1_relat_1(k7_relat_1(sK5,X0_55)) = k1_setfam_1(k2_tarski(sK3,X0_55)) ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_8518,c_2379]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_10086,plain,
% 13.95/2.49      ( k1_setfam_1(k2_tarski(sK3,sK2)) = k1_relat_1(k1_xboole_0) ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_10083,c_8521]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_6,plain,
% 13.95/2.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 13.95/2.49      inference(cnf_transformation,[],[f57]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_951,plain,
% 13.95/2.49      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_6]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_10087,plain,
% 13.95/2.49      ( k1_setfam_1(k2_tarski(sK3,sK2)) = k1_xboole_0 ),
% 13.95/2.49      inference(light_normalisation,[status(thm)],[c_10086,c_951]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_0,plain,
% 13.95/2.49      ( r1_xboole_0(X0,X1)
% 13.95/2.49      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 13.95/2.49      inference(cnf_transformation,[],[f89]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_260,plain,
% 13.95/2.49      ( r1_xboole_0(X0,X1)
% 13.95/2.49      | k1_setfam_1(k2_tarski(X0,X1)) != k1_xboole_0 ),
% 13.95/2.49      inference(prop_impl,[status(thm)],[c_0]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_563,plain,
% 13.95/2.49      ( ~ v1_relat_1(X0)
% 13.95/2.49      | X1 != X2
% 13.95/2.49      | k7_relat_1(X0,X1) = k1_xboole_0
% 13.95/2.49      | k1_relat_1(X0) != X3
% 13.95/2.49      | k1_setfam_1(k2_tarski(X2,X3)) != k1_xboole_0 ),
% 13.95/2.49      inference(resolution_lifted,[status(thm)],[c_260,c_3]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_564,plain,
% 13.95/2.49      ( ~ v1_relat_1(X0)
% 13.95/2.49      | k7_relat_1(X0,X1) = k1_xboole_0
% 13.95/2.49      | k1_setfam_1(k2_tarski(X1,k1_relat_1(X0))) != k1_xboole_0 ),
% 13.95/2.49      inference(unflattening,[status(thm)],[c_563]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_928,plain,
% 13.95/2.49      ( ~ v1_relat_1(X0_55)
% 13.95/2.49      | k7_relat_1(X0_55,X1_55) = k1_xboole_0
% 13.95/2.49      | k1_setfam_1(k2_tarski(X1_55,k1_relat_1(X0_55))) != k1_xboole_0 ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_564]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1459,plain,
% 13.95/2.49      ( k7_relat_1(X0_55,X1_55) = k1_xboole_0
% 13.95/2.49      | k1_setfam_1(k2_tarski(X1_55,k1_relat_1(X0_55))) != k1_xboole_0
% 13.95/2.49      | v1_relat_1(X0_55) != iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_928]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_25844,plain,
% 13.95/2.49      ( k7_relat_1(sK4,X0_55) = k1_xboole_0
% 13.95/2.49      | k1_setfam_1(k2_tarski(X0_55,sK2)) != k1_xboole_0
% 13.95/2.49      | v1_relat_1(sK4) != iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_8526,c_1459]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1778,plain,
% 13.95/2.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 13.95/2.49      | v1_relat_1(sK4) ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_949]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_25937,plain,
% 13.95/2.49      ( ~ v1_relat_1(sK4)
% 13.95/2.49      | k7_relat_1(sK4,X0_55) = k1_xboole_0
% 13.95/2.49      | k1_setfam_1(k2_tarski(X0_55,sK2)) != k1_xboole_0 ),
% 13.95/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_25844]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_26276,plain,
% 13.95/2.49      ( k1_setfam_1(k2_tarski(X0_55,sK2)) != k1_xboole_0
% 13.95/2.49      | k7_relat_1(sK4,X0_55) = k1_xboole_0 ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_25844,c_27,c_1778,c_25937]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_26277,plain,
% 13.95/2.49      ( k7_relat_1(sK4,X0_55) = k1_xboole_0
% 13.95/2.49      | k1_setfam_1(k2_tarski(X0_55,sK2)) != k1_xboole_0 ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_26276]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_26281,plain,
% 13.95/2.49      ( k7_relat_1(sK4,sK3) = k1_xboole_0 ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_10087,c_26277]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_29214,plain,
% 13.95/2.49      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 13.95/2.49      inference(light_normalisation,[status(thm)],[c_29208,c_26281]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2390,plain,
% 13.95/2.49      ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(k1_relat_1(sK5),X0_55))) = k7_relat_1(sK5,X0_55) ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_2269,c_1437]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_3300,plain,
% 13.95/2.49      ( k7_relat_1(sK5,k1_relat_1(k7_relat_1(sK5,X0_55))) = k7_relat_1(sK5,X0_55) ),
% 13.95/2.49      inference(light_normalisation,[status(thm)],[c_2390,c_2379]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_9773,plain,
% 13.95/2.49      ( k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK3,X0_55))) = k7_relat_1(sK5,X0_55) ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_8521,c_3300]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_27834,plain,
% 13.95/2.49      ( k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK5,sK2) ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_10087,c_9773]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_27840,plain,
% 13.95/2.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 13.95/2.49      inference(light_normalisation,[status(thm)],[c_27834,c_10083]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_31,negated_conjecture,
% 13.95/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 13.95/2.49      inference(cnf_transformation,[],[f80]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_936,negated_conjecture,
% 13.95/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_31]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1451,plain,
% 13.95/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_936]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2,plain,
% 13.95/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 13.95/2.49      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 13.95/2.49      inference(cnf_transformation,[],[f91]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_954,plain,
% 13.95/2.49      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(X1_55))
% 13.95/2.49      | k9_subset_1(X1_55,X2_55,X0_55) = k1_setfam_1(k2_tarski(X2_55,X0_55)) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_2]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1436,plain,
% 13.95/2.49      ( k9_subset_1(X0_55,X1_55,X2_55) = k1_setfam_1(k2_tarski(X1_55,X2_55))
% 13.95/2.49      | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2312,plain,
% 13.95/2.49      ( k9_subset_1(sK0,X0_55,sK3) = k1_setfam_1(k2_tarski(X0_55,sK3)) ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1451,c_1436]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_16,plain,
% 13.95/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 13.95/2.49      inference(cnf_transformation,[],[f68]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_948,plain,
% 13.95/2.49      ( ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 13.95/2.49      | ~ v1_funct_1(X0_55)
% 13.95/2.49      | k2_partfun1(X1_55,X2_55,X0_55,X3_55) = k7_relat_1(X0_55,X3_55) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_16]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1440,plain,
% 13.95/2.49      ( k2_partfun1(X0_55,X1_55,X2_55,X3_55) = k7_relat_1(X2_55,X3_55)
% 13.95/2.49      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 13.95/2.49      | v1_funct_1(X2_55) != iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_948]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2451,plain,
% 13.95/2.49      ( k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55)
% 13.95/2.49      | v1_funct_1(sK4) != iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1448,c_1440]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1852,plain,
% 13.95/2.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 13.95/2.49      | ~ v1_funct_1(sK4)
% 13.95/2.49      | k2_partfun1(X0_55,X1_55,sK4,X2_55) = k7_relat_1(sK4,X2_55) ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_948]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2037,plain,
% 13.95/2.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 13.95/2.49      | ~ v1_funct_1(sK4)
% 13.95/2.49      | k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_1852]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2702,plain,
% 13.95/2.49      ( k2_partfun1(sK2,sK1,sK4,X0_55) = k7_relat_1(sK4,X0_55) ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_2451,c_29,c_27,c_2037]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2450,plain,
% 13.95/2.49      ( k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55)
% 13.95/2.49      | v1_funct_1(sK5) != iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1445,c_1440]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1847,plain,
% 13.95/2.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 13.95/2.49      | ~ v1_funct_1(sK5)
% 13.95/2.49      | k2_partfun1(X0_55,X1_55,sK5,X2_55) = k7_relat_1(sK5,X2_55) ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_948]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2032,plain,
% 13.95/2.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 13.95/2.49      | ~ v1_funct_1(sK5)
% 13.95/2.49      | k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
% 13.95/2.49      inference(instantiation,[status(thm)],[c_1847]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2697,plain,
% 13.95/2.49      ( k2_partfun1(sK3,sK1,sK5,X0_55) = k7_relat_1(sK5,X0_55) ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_2450,c_26,c_24,c_2032]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_18,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ v1_funct_2(X3,X4,X2)
% 13.95/2.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 13.95/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 13.95/2.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | ~ v1_funct_1(X3)
% 13.95/2.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 13.95/2.49      | v1_xboole_0(X5)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | v1_xboole_0(X4)
% 13.95/2.49      | v1_xboole_0(X1)
% 13.95/2.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 13.95/2.49      inference(cnf_transformation,[],[f97]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_22,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ v1_funct_2(X3,X4,X2)
% 13.95/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | ~ v1_funct_1(X3)
% 13.95/2.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 13.95/2.49      | v1_xboole_0(X5)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | v1_xboole_0(X4)
% 13.95/2.49      | v1_xboole_0(X1) ),
% 13.95/2.49      inference(cnf_transformation,[],[f72]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_21,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ v1_funct_2(X3,X4,X2)
% 13.95/2.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 13.95/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | ~ v1_funct_1(X3)
% 13.95/2.49      | v1_xboole_0(X5)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | v1_xboole_0(X4)
% 13.95/2.49      | v1_xboole_0(X1) ),
% 13.95/2.49      inference(cnf_transformation,[],[f73]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ v1_funct_2(X3,X4,X2)
% 13.95/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 13.95/2.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | ~ v1_funct_1(X3)
% 13.95/2.49      | v1_xboole_0(X5)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | v1_xboole_0(X4)
% 13.95/2.49      | v1_xboole_0(X1) ),
% 13.95/2.49      inference(cnf_transformation,[],[f74]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_201,plain,
% 13.95/2.49      ( ~ v1_funct_1(X3)
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | ~ v1_funct_2(X3,X4,X2)
% 13.95/2.49      | ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 13.95/2.49      | v1_xboole_0(X5)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | v1_xboole_0(X4)
% 13.95/2.49      | v1_xboole_0(X1)
% 13.95/2.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_18,c_22,c_21,c_20]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_202,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ v1_funct_2(X3,X4,X2)
% 13.95/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | ~ v1_funct_1(X3)
% 13.95/2.49      | v1_xboole_0(X1)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | v1_xboole_0(X4)
% 13.95/2.49      | v1_xboole_0(X5)
% 13.95/2.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_201]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_929,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 13.95/2.49      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 13.95/2.49      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 13.95/2.49      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 13.95/2.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 13.95/2.49      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 13.95/2.49      | ~ v1_funct_1(X0_55)
% 13.95/2.49      | ~ v1_funct_1(X3_55)
% 13.95/2.49      | v1_xboole_0(X2_55)
% 13.95/2.49      | v1_xboole_0(X1_55)
% 13.95/2.49      | v1_xboole_0(X4_55)
% 13.95/2.49      | v1_xboole_0(X5_55)
% 13.95/2.49      | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X1_55) = X0_55 ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_202]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1458,plain,
% 13.95/2.49      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X0_55) = X2_55
% 13.95/2.49      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 13.95/2.49      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 13.95/2.49      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 13.95/2.49      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 13.95/2.49      | v1_funct_1(X2_55) != iProver_top
% 13.95/2.49      | v1_funct_1(X5_55) != iProver_top
% 13.95/2.49      | v1_xboole_0(X3_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X1_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X4_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_929]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_6726,plain,
% 13.95/2.49      ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),sK3) = sK5
% 13.95/2.49      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 13.95/2.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | v1_funct_1(X1_55) != iProver_top
% 13.95/2.49      | v1_funct_1(sK5) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(sK1) = iProver_top
% 13.95/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_2697,c_1458]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_38,plain,
% 13.95/2.49      ( v1_xboole_0(sK1) != iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_41,plain,
% 13.95/2.49      ( v1_xboole_0(sK3) != iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_47,plain,
% 13.95/2.49      ( v1_funct_1(sK5) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_48,plain,
% 13.95/2.49      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_49,plain,
% 13.95/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20021,plain,
% 13.95/2.49      ( v1_funct_1(X1_55) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 13.95/2.49      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),sK3) = sK5
% 13.95/2.49      | k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_6726,c_38,c_41,c_47,c_48,c_49]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20022,plain,
% 13.95/2.49      ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),sK3) = sK5
% 13.95/2.49      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | v1_funct_1(X1_55) != iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_20021]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20037,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 13.95/2.49      | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
% 13.95/2.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 13.95/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | v1_funct_1(sK4) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(sK2) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_2702,c_20022]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_39,plain,
% 13.95/2.49      ( v1_xboole_0(sK2) != iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_44,plain,
% 13.95/2.49      ( v1_funct_1(sK4) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_45,plain,
% 13.95/2.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_46,plain,
% 13.95/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20206,plain,
% 13.95/2.49      ( v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 13.95/2.49      | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_20037,c_39,c_44,c_45,c_46]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20207,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 13.95/2.49      | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_20206]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20217,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 13.95/2.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK0) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_2312,c_20207]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20218,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 13.95/2.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK0) = iProver_top ),
% 13.95/2.49      inference(light_normalisation,[status(thm)],[c_20217,c_927]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_946,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 13.95/2.49      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 13.95/2.49      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 13.95/2.49      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 13.95/2.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 13.95/2.49      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 13.95/2.49      | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55)))
% 13.95/2.49      | ~ v1_funct_1(X0_55)
% 13.95/2.49      | ~ v1_funct_1(X3_55)
% 13.95/2.49      | v1_xboole_0(X2_55)
% 13.95/2.49      | v1_xboole_0(X1_55)
% 13.95/2.49      | v1_xboole_0(X4_55)
% 13.95/2.49      | v1_xboole_0(X5_55) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_20]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1442,plain,
% 13.95/2.49      ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
% 13.95/2.49      | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
% 13.95/2.49      | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 13.95/2.49      | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
% 13.95/2.49      | m1_subset_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_55,X4_55,X1_55),X2_55))) = iProver_top
% 13.95/2.49      | v1_funct_1(X0_55) != iProver_top
% 13.95/2.49      | v1_funct_1(X3_55) != iProver_top
% 13.95/2.49      | v1_xboole_0(X5_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X4_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X1_55) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_946]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_3143,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
% 13.95/2.49      | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
% 13.95/2.49      | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
% 13.95/2.49      | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
% 13.95/2.49      | v1_funct_1(X5_55) != iProver_top
% 13.95/2.49      | v1_funct_1(X4_55) != iProver_top
% 13.95/2.49      | v1_funct_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55)) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X3_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X1_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1442,c_1440]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_944,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 13.95/2.49      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 13.95/2.49      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 13.95/2.49      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 13.95/2.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 13.95/2.49      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 13.95/2.49      | ~ v1_funct_1(X0_55)
% 13.95/2.49      | ~ v1_funct_1(X3_55)
% 13.95/2.49      | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55))
% 13.95/2.49      | v1_xboole_0(X2_55)
% 13.95/2.49      | v1_xboole_0(X1_55)
% 13.95/2.49      | v1_xboole_0(X4_55)
% 13.95/2.49      | v1_xboole_0(X5_55) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_22]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1444,plain,
% 13.95/2.49      ( v1_funct_2(X0_55,X1_55,X2_55) != iProver_top
% 13.95/2.49      | v1_funct_2(X3_55,X4_55,X2_55) != iProver_top
% 13.95/2.49      | m1_subset_1(X4_55,k1_zfmisc_1(X5_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(X5_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55))) != iProver_top
% 13.95/2.49      | m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55))) != iProver_top
% 13.95/2.49      | v1_funct_1(X0_55) != iProver_top
% 13.95/2.49      | v1_funct_1(X3_55) != iProver_top
% 13.95/2.49      | v1_funct_1(k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55)) = iProver_top
% 13.95/2.49      | v1_xboole_0(X5_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X4_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X1_55) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_944]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11002,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(X0_55,X1_55,X2_55),X3_55,k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55) = k7_relat_1(k1_tmap_1(X0_55,X3_55,X1_55,X2_55,X4_55,X5_55),X6_55)
% 13.95/2.49      | v1_funct_2(X5_55,X2_55,X3_55) != iProver_top
% 13.95/2.49      | v1_funct_2(X4_55,X1_55,X3_55) != iProver_top
% 13.95/2.49      | m1_subset_1(X2_55,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X2_55,X3_55))) != iProver_top
% 13.95/2.49      | m1_subset_1(X4_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X3_55))) != iProver_top
% 13.95/2.49      | v1_funct_1(X5_55) != iProver_top
% 13.95/2.49      | v1_funct_1(X4_55) != iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X1_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X3_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top ),
% 13.95/2.49      inference(forward_subsumption_resolution,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_3143,c_1444]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11006,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
% 13.95/2.49      | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
% 13.95/2.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | v1_funct_1(X2_55) != iProver_top
% 13.95/2.49      | v1_funct_1(sK5) != iProver_top
% 13.95/2.49      | v1_xboole_0(X1_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(sK1) = iProver_top
% 13.95/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1445,c_11002]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11113,plain,
% 13.95/2.49      ( v1_funct_1(X2_55) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
% 13.95/2.49      | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
% 13.95/2.49      | v1_xboole_0(X1_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_11006,c_38,c_41,c_47,c_48]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11114,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(X0_55,X1_55,sK3),sK1,k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,X1_55,sK3,X2_55,sK5),X3_55)
% 13.95/2.49      | v1_funct_2(X2_55,X1_55,sK1) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | v1_funct_1(X2_55) != iProver_top
% 13.95/2.49      | v1_xboole_0(X1_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_11113]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11128,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55)
% 13.95/2.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | v1_funct_1(sK4) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(sK2) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1448,c_11114]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11545,plain,
% 13.95/2.49      ( v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55)
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_11128,c_39,c_44,c_45]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11546,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55) = k7_relat_1(k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),X1_55)
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_11545]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11555,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55)
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK0) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_1451,c_11546]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_36,negated_conjecture,
% 13.95/2.49      ( ~ v1_xboole_0(sK0) ),
% 13.95/2.49      inference(cnf_transformation,[],[f75]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_37,plain,
% 13.95/2.49      ( v1_xboole_0(sK0) != iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_33,negated_conjecture,
% 13.95/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 13.95/2.49      inference(cnf_transformation,[],[f78]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_40,plain,
% 13.95/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11560,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_55) ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_11555,c_37,c_40]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20219,plain,
% 13.95/2.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 13.95/2.49      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK0) = iProver_top ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_20218,c_2312,c_11560]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20220,plain,
% 13.95/2.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 13.95/2.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK0) = iProver_top ),
% 13.95/2.49      inference(light_normalisation,[status(thm)],[c_20219,c_927]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_23,negated_conjecture,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 13.95/2.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 13.95/2.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 13.95/2.49      inference(cnf_transformation,[],[f88]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_943,negated_conjecture,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 13.95/2.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 13.95/2.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_23]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2504,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 13.95/2.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 13.95/2.49      | k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_2312,c_943]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2505,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 13.95/2.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 13.95/2.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 13.95/2.49      inference(light_normalisation,[status(thm)],[c_2504,c_927]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_2741,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 13.95/2.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 13.95/2.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_2505,c_2697,c_2702]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11564,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 13.95/2.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 13.95/2.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_11560,c_2741]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_11565,plain,
% 13.95/2.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 13.95/2.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 13.95/2.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_11564,c_11560]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_19,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ v1_funct_2(X3,X4,X2)
% 13.95/2.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 13.95/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 13.95/2.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | ~ v1_funct_1(X3)
% 13.95/2.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 13.95/2.49      | v1_xboole_0(X5)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | v1_xboole_0(X4)
% 13.95/2.49      | v1_xboole_0(X1)
% 13.95/2.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 13.95/2.49      inference(cnf_transformation,[],[f98]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_194,plain,
% 13.95/2.49      ( ~ v1_funct_1(X3)
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | ~ v1_funct_2(X3,X4,X2)
% 13.95/2.49      | ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 13.95/2.49      | v1_xboole_0(X5)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | v1_xboole_0(X4)
% 13.95/2.49      | v1_xboole_0(X1)
% 13.95/2.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_19,c_22,c_21,c_20]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_195,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0,X1,X2)
% 13.95/2.49      | ~ v1_funct_2(X3,X4,X2)
% 13.95/2.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 13.95/2.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 13.95/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 13.95/2.49      | ~ v1_funct_1(X0)
% 13.95/2.49      | ~ v1_funct_1(X3)
% 13.95/2.49      | v1_xboole_0(X1)
% 13.95/2.49      | v1_xboole_0(X2)
% 13.95/2.49      | v1_xboole_0(X4)
% 13.95/2.49      | v1_xboole_0(X5)
% 13.95/2.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_194]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_930,plain,
% 13.95/2.49      ( ~ v1_funct_2(X0_55,X1_55,X2_55)
% 13.95/2.49      | ~ v1_funct_2(X3_55,X4_55,X2_55)
% 13.95/2.49      | ~ m1_subset_1(X4_55,k1_zfmisc_1(X5_55))
% 13.95/2.49      | ~ m1_subset_1(X1_55,k1_zfmisc_1(X5_55))
% 13.95/2.49      | ~ m1_subset_1(X0_55,k1_zfmisc_1(k2_zfmisc_1(X1_55,X2_55)))
% 13.95/2.49      | ~ m1_subset_1(X3_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X2_55)))
% 13.95/2.49      | ~ v1_funct_1(X0_55)
% 13.95/2.49      | ~ v1_funct_1(X3_55)
% 13.95/2.49      | v1_xboole_0(X2_55)
% 13.95/2.49      | v1_xboole_0(X1_55)
% 13.95/2.49      | v1_xboole_0(X4_55)
% 13.95/2.49      | v1_xboole_0(X5_55)
% 13.95/2.49      | k2_partfun1(X1_55,X2_55,X0_55,k9_subset_1(X5_55,X4_55,X1_55)) != k2_partfun1(X4_55,X2_55,X3_55,k9_subset_1(X5_55,X4_55,X1_55))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X5_55,X4_55,X1_55),X2_55,k1_tmap_1(X5_55,X2_55,X4_55,X1_55,X3_55,X0_55),X4_55) = X3_55 ),
% 13.95/2.49      inference(subtyping,[status(esa)],[c_195]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_1457,plain,
% 13.95/2.49      ( k2_partfun1(X0_55,X1_55,X2_55,k9_subset_1(X3_55,X4_55,X0_55)) != k2_partfun1(X4_55,X1_55,X5_55,k9_subset_1(X3_55,X4_55,X0_55))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X3_55,X4_55,X0_55),X1_55,k1_tmap_1(X3_55,X1_55,X4_55,X0_55,X5_55,X2_55),X4_55) = X5_55
% 13.95/2.49      | v1_funct_2(X2_55,X0_55,X1_55) != iProver_top
% 13.95/2.49      | v1_funct_2(X5_55,X4_55,X1_55) != iProver_top
% 13.95/2.49      | m1_subset_1(X4_55,k1_zfmisc_1(X3_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(X3_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X2_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 13.95/2.49      | m1_subset_1(X5_55,k1_zfmisc_1(k2_zfmisc_1(X4_55,X1_55))) != iProver_top
% 13.95/2.49      | v1_funct_1(X2_55) != iProver_top
% 13.95/2.49      | v1_funct_1(X5_55) != iProver_top
% 13.95/2.49      | v1_xboole_0(X3_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X1_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X4_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top ),
% 13.95/2.49      inference(predicate_to_equality,[status(thm)],[c_930]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_4581,plain,
% 13.95/2.49      ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),X0_55) = X1_55
% 13.95/2.49      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 13.95/2.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | v1_funct_1(X1_55) != iProver_top
% 13.95/2.49      | v1_funct_1(sK5) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(sK1) = iProver_top
% 13.95/2.49      | v1_xboole_0(sK3) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_2697,c_1457]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_8289,plain,
% 13.95/2.49      ( v1_funct_1(X1_55) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 13.95/2.49      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),X0_55) = X1_55
% 13.95/2.49      | k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_4581,c_38,c_41,c_47,c_48,c_49]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_8290,plain,
% 13.95/2.49      ( k2_partfun1(X0_55,sK1,X1_55,k9_subset_1(X2_55,X0_55,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_55,X0_55,sK3))
% 13.95/2.49      | k2_partfun1(k4_subset_1(X2_55,X0_55,sK3),sK1,k1_tmap_1(X2_55,sK1,X0_55,sK3,X1_55,sK5),X0_55) = X1_55
% 13.95/2.49      | v1_funct_2(X1_55,X0_55,sK1) != iProver_top
% 13.95/2.49      | m1_subset_1(X0_55,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(X1_55,k1_zfmisc_1(k2_zfmisc_1(X0_55,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_55)) != iProver_top
% 13.95/2.49      | v1_funct_1(X1_55) != iProver_top
% 13.95/2.49      | v1_xboole_0(X2_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_8289]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_8305,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 13.95/2.49      | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
% 13.95/2.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 13.95/2.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | v1_funct_1(sK4) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | v1_xboole_0(sK2) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_2702,c_8290]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_16559,plain,
% 13.95/2.49      ( v1_xboole_0(X0_55) = iProver_top
% 13.95/2.49      | k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 13.95/2.49      | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_8305,c_39,c_44,c_45,c_46]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_16560,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(X0_55,sK2,sK3),sK1,k1_tmap_1(X0_55,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 13.95/2.49      | k7_relat_1(sK5,k9_subset_1(X0_55,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_55,sK2,sK3))
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_55)) != iProver_top
% 13.95/2.49      | v1_xboole_0(X0_55) = iProver_top ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_16559]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_16570,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 13.95/2.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK0) = iProver_top ),
% 13.95/2.49      inference(superposition,[status(thm)],[c_2312,c_16560]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_16571,plain,
% 13.95/2.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 13.95/2.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k1_xboole_0)
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK0) = iProver_top ),
% 13.95/2.49      inference(light_normalisation,[status(thm)],[c_16570,c_927]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_16572,plain,
% 13.95/2.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 13.95/2.49      | k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_xboole_0)
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK0) = iProver_top ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_16571,c_2312,c_11560]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_16573,plain,
% 13.95/2.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 13.95/2.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 13.95/2.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 13.95/2.49      | v1_xboole_0(sK0) = iProver_top ),
% 13.95/2.49      inference(light_normalisation,[status(thm)],[c_16572,c_927]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_16574,plain,
% 13.95/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 13.95/2.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 13.95/2.49      | v1_xboole_0(sK0)
% 13.95/2.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 13.95/2.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 13.95/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_16573]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_16576,plain,
% 13.95/2.49      ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
% 13.95/2.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_16573,c_36,c_33,c_31,c_16574]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_16577,plain,
% 13.95/2.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 13.95/2.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 13.95/2.49      inference(renaming,[status(thm)],[c_16576]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20221,plain,
% 13.95/2.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 13.95/2.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 13.95/2.49      | v1_xboole_0(sK0)
% 13.95/2.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 13.95/2.49      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 13.95/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_20220]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_20223,plain,
% 13.95/2.49      ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 13.95/2.49      inference(global_propositional_subsumption,
% 13.95/2.49                [status(thm)],
% 13.95/2.49                [c_20220,c_36,c_33,c_31,c_11565,c_16577,c_20221]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(c_27846,plain,
% 13.95/2.49      ( k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 13.95/2.49      inference(demodulation,[status(thm)],[c_27840,c_20223]) ).
% 13.95/2.49  
% 13.95/2.49  cnf(contradiction,plain,
% 13.95/2.49      ( $false ),
% 13.95/2.49      inference(minisat,[status(thm)],[c_29214,c_27846]) ).
% 13.95/2.49  
% 13.95/2.49  
% 13.95/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 13.95/2.49  
% 13.95/2.49  ------                               Statistics
% 13.95/2.49  
% 13.95/2.49  ------ General
% 13.95/2.49  
% 13.95/2.49  abstr_ref_over_cycles:                  0
% 13.95/2.49  abstr_ref_under_cycles:                 0
% 13.95/2.49  gc_basic_clause_elim:                   0
% 13.95/2.49  forced_gc_time:                         0
% 13.95/2.49  parsing_time:                           0.013
% 13.95/2.49  unif_index_cands_time:                  0.
% 13.95/2.49  unif_index_add_time:                    0.
% 13.95/2.49  orderings_time:                         0.
% 13.95/2.49  out_proof_time:                         0.021
% 13.95/2.49  total_time:                             1.613
% 13.95/2.49  num_of_symbols:                         61
% 13.95/2.49  num_of_terms:                           53232
% 13.95/2.49  
% 13.95/2.49  ------ Preprocessing
% 13.95/2.49  
% 13.95/2.49  num_of_splits:                          0
% 13.95/2.49  num_of_split_atoms:                     0
% 13.95/2.49  num_of_reused_defs:                     0
% 13.95/2.49  num_eq_ax_congr_red:                    10
% 13.95/2.49  num_of_sem_filtered_clauses:            1
% 13.95/2.49  num_of_subtypes:                        3
% 13.95/2.49  monotx_restored_types:                  0
% 13.95/2.49  sat_num_of_epr_types:                   0
% 13.95/2.49  sat_num_of_non_cyclic_types:            0
% 13.95/2.49  sat_guarded_non_collapsed_types:        1
% 13.95/2.49  num_pure_diseq_elim:                    0
% 13.95/2.49  simp_replaced_by:                       0
% 13.95/2.49  res_preprocessed:                       165
% 13.95/2.49  prep_upred:                             0
% 13.95/2.49  prep_unflattend:                        12
% 13.95/2.49  smt_new_axioms:                         0
% 13.95/2.49  pred_elim_cands:                        5
% 13.95/2.49  pred_elim:                              4
% 13.95/2.49  pred_elim_cl:                           6
% 13.95/2.49  pred_elim_cycles:                       7
% 13.95/2.49  merged_defs:                            2
% 13.95/2.49  merged_defs_ncl:                        0
% 13.95/2.49  bin_hyper_res:                          2
% 13.95/2.49  prep_cycles:                            4
% 13.95/2.49  pred_elim_time:                         0.007
% 13.95/2.49  splitting_time:                         0.
% 13.95/2.49  sem_filter_time:                        0.
% 13.95/2.49  monotx_time:                            0.
% 13.95/2.49  subtype_inf_time:                       0.001
% 13.95/2.49  
% 13.95/2.49  ------ Problem properties
% 13.95/2.49  
% 13.95/2.49  clauses:                                30
% 13.95/2.49  conjectures:                            13
% 13.95/2.49  epr:                                    8
% 13.95/2.49  horn:                                   23
% 13.95/2.49  ground:                                 16
% 13.95/2.49  unary:                                  15
% 13.95/2.49  binary:                                 4
% 13.95/2.49  lits:                                   124
% 13.95/2.49  lits_eq:                                21
% 13.95/2.49  fd_pure:                                0
% 13.95/2.49  fd_pseudo:                              0
% 13.95/2.49  fd_cond:                                0
% 13.95/2.49  fd_pseudo_cond:                         1
% 13.95/2.49  ac_symbols:                             0
% 13.95/2.49  
% 13.95/2.49  ------ Propositional Solver
% 13.95/2.49  
% 13.95/2.49  prop_solver_calls:                      30
% 13.95/2.49  prop_fast_solver_calls:                 5688
% 13.95/2.49  smt_solver_calls:                       0
% 13.95/2.49  smt_fast_solver_calls:                  0
% 13.95/2.49  prop_num_of_clauses:                    11800
% 13.95/2.49  prop_preprocess_simplified:             21831
% 13.95/2.49  prop_fo_subsumed:                       511
% 13.95/2.49  prop_solver_time:                       0.
% 13.95/2.49  smt_solver_time:                        0.
% 13.95/2.49  smt_fast_solver_time:                   0.
% 13.95/2.49  prop_fast_solver_time:                  0.
% 13.95/2.49  prop_unsat_core_time:                   0.001
% 13.95/2.49  
% 13.95/2.49  ------ QBF
% 13.95/2.49  
% 13.95/2.49  qbf_q_res:                              0
% 13.95/2.49  qbf_num_tautologies:                    0
% 13.95/2.49  qbf_prep_cycles:                        0
% 13.95/2.49  
% 13.95/2.49  ------ BMC1
% 13.95/2.49  
% 13.95/2.49  bmc1_current_bound:                     -1
% 13.95/2.49  bmc1_last_solved_bound:                 -1
% 13.95/2.49  bmc1_unsat_core_size:                   -1
% 13.95/2.49  bmc1_unsat_core_parents_size:           -1
% 13.95/2.49  bmc1_merge_next_fun:                    0
% 13.95/2.49  bmc1_unsat_core_clauses_time:           0.
% 13.95/2.49  
% 13.95/2.49  ------ Instantiation
% 13.95/2.49  
% 13.95/2.49  inst_num_of_clauses:                    2667
% 13.95/2.49  inst_num_in_passive:                    417
% 13.95/2.49  inst_num_in_active:                     1396
% 13.95/2.49  inst_num_in_unprocessed:                854
% 13.95/2.49  inst_num_of_loops:                      1410
% 13.95/2.49  inst_num_of_learning_restarts:          0
% 13.95/2.49  inst_num_moves_active_passive:          8
% 13.95/2.49  inst_lit_activity:                      0
% 13.95/2.49  inst_lit_activity_moves:                0
% 13.95/2.49  inst_num_tautologies:                   0
% 13.95/2.49  inst_num_prop_implied:                  0
% 13.95/2.49  inst_num_existing_simplified:           0
% 13.95/2.49  inst_num_eq_res_simplified:             0
% 13.95/2.49  inst_num_child_elim:                    0
% 13.95/2.49  inst_num_of_dismatching_blockings:      276
% 13.95/2.49  inst_num_of_non_proper_insts:           2318
% 13.95/2.49  inst_num_of_duplicates:                 0
% 13.95/2.49  inst_inst_num_from_inst_to_res:         0
% 13.95/2.49  inst_dismatching_checking_time:         0.
% 13.95/2.49  
% 13.95/2.49  ------ Resolution
% 13.95/2.49  
% 13.95/2.49  res_num_of_clauses:                     0
% 13.95/2.49  res_num_in_passive:                     0
% 13.95/2.49  res_num_in_active:                      0
% 13.95/2.49  res_num_of_loops:                       169
% 13.95/2.49  res_forward_subset_subsumed:            50
% 13.95/2.49  res_backward_subset_subsumed:           4
% 13.95/2.49  res_forward_subsumed:                   0
% 13.95/2.49  res_backward_subsumed:                  0
% 13.95/2.49  res_forward_subsumption_resolution:     1
% 13.95/2.49  res_backward_subsumption_resolution:    0
% 13.95/2.49  res_clause_to_clause_subsumption:       4048
% 13.95/2.49  res_orphan_elimination:                 0
% 13.95/2.49  res_tautology_del:                      48
% 13.95/2.49  res_num_eq_res_simplified:              0
% 13.95/2.49  res_num_sel_changes:                    0
% 13.95/2.49  res_moves_from_active_to_pass:          0
% 13.95/2.49  
% 13.95/2.49  ------ Superposition
% 13.95/2.49  
% 13.95/2.49  sup_time_total:                         0.
% 13.95/2.49  sup_time_generating:                    0.
% 13.95/2.49  sup_time_sim_full:                      0.
% 13.95/2.49  sup_time_sim_immed:                     0.
% 13.95/2.49  
% 13.95/2.49  sup_num_of_clauses:                     425
% 13.95/2.49  sup_num_in_active:                      251
% 13.95/2.49  sup_num_in_passive:                     174
% 13.95/2.49  sup_num_of_loops:                       281
% 13.95/2.49  sup_fw_superposition:                   373
% 13.95/2.49  sup_bw_superposition:                   101
% 13.95/2.49  sup_immediate_simplified:               279
% 13.95/2.49  sup_given_eliminated:                   0
% 13.95/2.49  comparisons_done:                       0
% 13.95/2.49  comparisons_avoided:                    0
% 13.95/2.49  
% 13.95/2.49  ------ Simplifications
% 13.95/2.49  
% 13.95/2.49  
% 13.95/2.49  sim_fw_subset_subsumed:                 4
% 13.95/2.49  sim_bw_subset_subsumed:                 1
% 13.95/2.49  sim_fw_subsumed:                        40
% 13.95/2.49  sim_bw_subsumed:                        3
% 13.95/2.49  sim_fw_subsumption_res:                 16
% 13.95/2.49  sim_bw_subsumption_res:                 1
% 13.95/2.49  sim_tautology_del:                      0
% 13.95/2.49  sim_eq_tautology_del:                   7
% 13.95/2.49  sim_eq_res_simp:                        2
% 13.95/2.49  sim_fw_demodulated:                     182
% 13.95/2.49  sim_bw_demodulated:                     31
% 13.95/2.49  sim_light_normalised:                   129
% 13.95/2.49  sim_joinable_taut:                      0
% 13.95/2.49  sim_joinable_simp:                      0
% 13.95/2.49  sim_ac_normalised:                      0
% 13.95/2.49  sim_smt_subsumption:                    0
% 13.95/2.49  
%------------------------------------------------------------------------------
