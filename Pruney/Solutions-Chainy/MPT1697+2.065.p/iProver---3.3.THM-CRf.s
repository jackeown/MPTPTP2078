%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:37 EST 2020

% Result     : Theorem 7.29s
% Output     : CNFRefutation 7.29s
% Verified   : 
% Statistics : Number of formulae       :  223 (3022 expanded)
%              Number of clauses        :  150 ( 796 expanded)
%              Number of leaves         :   18 (1146 expanded)
%              Depth                    :   26
%              Number of atoms          : 1267 (37416 expanded)
%              Number of equality atoms :  564 (9023 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f55,plain,(
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

fof(f76,plain,(
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
    inference(equality_resolution,[],[f55])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f57,plain,(
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

fof(f58,plain,(
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

fof(f59,plain,(
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

fof(f61,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

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

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f42])).

fof(f54,plain,(
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

fof(f77,plain,(
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
    inference(equality_resolution,[],[f54])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_718,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1189,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_732,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1176,plain,
    ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_2353,plain,
    ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
    inference(superposition,[status(thm)],[c_1189,c_1176])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_721,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1186,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_730,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1178,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_2410,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_1178])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1564,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_1732,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_1564])).

cnf(c_2756,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2410,c_23,c_21,c_1732])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_724,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1183,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_2409,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1178])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1559,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_1727,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(instantiation,[status(thm)],[c_1559])).

cnf(c_2751,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2409,c_20,c_18,c_1727])).

cnf(c_12,plain,
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
    inference(cnf_transformation,[],[f76])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f57])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f58])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f59])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_16,c_15,c_14])).

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

cnf(c_711,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51)
    | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
    | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X1_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_174])).

cnf(c_1196,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
    | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X0_51) = X2_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_5607,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2751,c_1196])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_32,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_35,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17815,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5607,c_32,c_35,c_41,c_42,c_43])).

cnf(c_17816,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_17815])).

cnf(c_17831,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_17816])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_33,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_39,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17965,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17831,c_33,c_38,c_39,c_40])).

cnf(c_17966,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_17965])).

cnf(c_17976,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2353,c_17966])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_224,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_435,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_24])).

cnf(c_436,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_438,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_28,c_26])).

cnf(c_475,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_224,c_438])).

cnf(c_476,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_707,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_476])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_396,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_9,c_5])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_400,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_9,c_8,c_5])).

cnf(c_710,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | k7_relat_1(X0_51,X1_51) = X0_51 ),
    inference(subtyping,[status(esa)],[c_400])).

cnf(c_1197,plain,
    ( k7_relat_1(X0_51,X1_51) = X0_51
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_2864,plain,
    ( k7_relat_1(sK5,sK3) = sK5 ),
    inference(superposition,[status(thm)],[c_1183,c_1197])).

cnf(c_731,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1177,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_2139,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1177])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_733,plain,
    ( k3_xboole_0(X0_51,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_222,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_448,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
    | k3_xboole_0(X1,X2) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_222,c_4])).

cnf(c_709,plain,
    ( ~ v1_relat_1(X0_51)
    | k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k1_xboole_0
    | k3_xboole_0(X1_51,X2_51) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_448])).

cnf(c_1198,plain,
    ( k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k1_xboole_0
    | k3_xboole_0(X1_51,X2_51) != k1_xboole_0
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_3472,plain,
    ( k7_relat_1(k7_relat_1(X0_51,X1_51),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_733,c_1198])).

cnf(c_3810,plain,
    ( k7_relat_1(k7_relat_1(sK5,X0_51),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2139,c_3472])).

cnf(c_3878,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2864,c_3810])).

cnf(c_17977,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17976,c_707,c_3878])).

cnf(c_728,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1180,plain,
    ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
    | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_xboole_0(X5_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_2514,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
    | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
    | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_funct_1(X4_51) != iProver_top
    | v1_funct_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(superposition,[status(thm)],[c_1180,c_1178])).

cnf(c_726,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51))
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1182,plain,
    ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
    | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51)) = iProver_top
    | v1_xboole_0(X5_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_8671,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
    | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
    | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_funct_1(X4_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2514,c_1182])).

cnf(c_8675,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_8671])).

cnf(c_9290,plain,
    ( v1_funct_1(X2_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8675,c_32,c_35,c_41,c_42])).

cnf(c_9291,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_9290])).

cnf(c_9305,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_9291])).

cnf(c_9891,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9305,c_33,c_38,c_39])).

cnf(c_9892,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_9891])).

cnf(c_9901,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1189,c_9892])).

cnf(c_30,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_9943,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9901,c_31,c_34])).

cnf(c_17978,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_17977,c_2353,c_9943])).

cnf(c_2865,plain,
    ( k7_relat_1(sK4,sK2) = sK4 ),
    inference(superposition,[status(thm)],[c_1186,c_1197])).

cnf(c_2140,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_1177])).

cnf(c_3811,plain,
    ( k7_relat_1(k7_relat_1(sK4,X0_51),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2140,c_3472])).

cnf(c_3933,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2865,c_3811])).

cnf(c_17979,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17978,c_707,c_3933])).

cnf(c_17980,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_17979])).

cnf(c_17,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_725,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2645,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2353,c_725])).

cnf(c_2646,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2645,c_707])).

cnf(c_2857,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_2646,c_2751,c_2756])).

cnf(c_3880,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3878,c_2857])).

cnf(c_17581,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3880,c_3933])).

cnf(c_17582,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_17581])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
    inference(cnf_transformation,[],[f77])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_16,c_15,c_14])).

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

cnf(c_712,plain,
    ( ~ v1_funct_2(X0_51,X1_51,X2_51)
    | ~ v1_funct_2(X3_51,X4_51,X2_51)
    | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X3_51)
    | v1_xboole_0(X1_51)
    | v1_xboole_0(X2_51)
    | v1_xboole_0(X4_51)
    | v1_xboole_0(X5_51)
    | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
    | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X4_51) = X3_51 ),
    inference(subtyping,[status(esa)],[c_167])).

cnf(c_1195,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
    | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X4_51) = X5_51
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_4164,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2751,c_1195])).

cnf(c_11963,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4164,c_32,c_35,c_41,c_42,c_43])).

cnf(c_11964,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
    | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_11963])).

cnf(c_11984,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2353,c_11964])).

cnf(c_11994,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11984,c_2353])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_12454,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11994,c_31,c_36])).

cnf(c_12455,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
    | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_12454])).

cnf(c_12468,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_12455])).

cnf(c_12552,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12468,c_707,c_3878,c_3933])).

cnf(c_12553,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12552])).

cnf(c_12554,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12553,c_9943])).

cnf(c_11979,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2756,c_11964])).

cnf(c_12436,plain,
    ( v1_xboole_0(X0_51) = iProver_top
    | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11979,c_33,c_38,c_39,c_40])).

cnf(c_12437,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_12436])).

cnf(c_12447,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2353,c_12437])).

cnf(c_12448,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12447,c_707,c_3878])).

cnf(c_12449,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12448,c_2353,c_9943])).

cnf(c_12450,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12449,c_707,c_3933])).

cnf(c_12451,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_xboole_0(sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_12450])).

cnf(c_12642,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12554,c_31,c_34,c_36,c_12451])).

cnf(c_17583,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | sK4 != sK4 ),
    inference(demodulation,[status(thm)],[c_17582,c_9943,c_12642])).

cnf(c_17584,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_17583])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17980,c_17584,c_36,c_34,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.29/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.29/1.49  
% 7.29/1.49  ------  iProver source info
% 7.29/1.49  
% 7.29/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.29/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.29/1.49  git: non_committed_changes: false
% 7.29/1.49  git: last_make_outside_of_git: false
% 7.29/1.49  
% 7.29/1.49  ------ 
% 7.29/1.49  
% 7.29/1.49  ------ Input Options
% 7.29/1.49  
% 7.29/1.49  --out_options                           all
% 7.29/1.49  --tptp_safe_out                         true
% 7.29/1.49  --problem_path                          ""
% 7.29/1.49  --include_path                          ""
% 7.29/1.49  --clausifier                            res/vclausify_rel
% 7.29/1.49  --clausifier_options                    --mode clausify
% 7.29/1.49  --stdin                                 false
% 7.29/1.49  --stats_out                             all
% 7.29/1.49  
% 7.29/1.49  ------ General Options
% 7.29/1.49  
% 7.29/1.49  --fof                                   false
% 7.29/1.49  --time_out_real                         305.
% 7.29/1.49  --time_out_virtual                      -1.
% 7.29/1.49  --symbol_type_check                     false
% 7.29/1.49  --clausify_out                          false
% 7.29/1.49  --sig_cnt_out                           false
% 7.29/1.49  --trig_cnt_out                          false
% 7.29/1.49  --trig_cnt_out_tolerance                1.
% 7.29/1.49  --trig_cnt_out_sk_spl                   false
% 7.29/1.49  --abstr_cl_out                          false
% 7.29/1.49  
% 7.29/1.49  ------ Global Options
% 7.29/1.49  
% 7.29/1.49  --schedule                              default
% 7.29/1.49  --add_important_lit                     false
% 7.29/1.49  --prop_solver_per_cl                    1000
% 7.29/1.49  --min_unsat_core                        false
% 7.29/1.49  --soft_assumptions                      false
% 7.29/1.49  --soft_lemma_size                       3
% 7.29/1.49  --prop_impl_unit_size                   0
% 7.29/1.49  --prop_impl_unit                        []
% 7.29/1.49  --share_sel_clauses                     true
% 7.29/1.49  --reset_solvers                         false
% 7.29/1.49  --bc_imp_inh                            [conj_cone]
% 7.29/1.49  --conj_cone_tolerance                   3.
% 7.29/1.49  --extra_neg_conj                        none
% 7.29/1.49  --large_theory_mode                     true
% 7.29/1.49  --prolific_symb_bound                   200
% 7.29/1.49  --lt_threshold                          2000
% 7.29/1.49  --clause_weak_htbl                      true
% 7.29/1.49  --gc_record_bc_elim                     false
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing Options
% 7.29/1.49  
% 7.29/1.49  --preprocessing_flag                    true
% 7.29/1.49  --time_out_prep_mult                    0.1
% 7.29/1.49  --splitting_mode                        input
% 7.29/1.49  --splitting_grd                         true
% 7.29/1.49  --splitting_cvd                         false
% 7.29/1.49  --splitting_cvd_svl                     false
% 7.29/1.49  --splitting_nvd                         32
% 7.29/1.49  --sub_typing                            true
% 7.29/1.49  --prep_gs_sim                           true
% 7.29/1.49  --prep_unflatten                        true
% 7.29/1.49  --prep_res_sim                          true
% 7.29/1.49  --prep_upred                            true
% 7.29/1.49  --prep_sem_filter                       exhaustive
% 7.29/1.49  --prep_sem_filter_out                   false
% 7.29/1.49  --pred_elim                             true
% 7.29/1.49  --res_sim_input                         true
% 7.29/1.49  --eq_ax_congr_red                       true
% 7.29/1.49  --pure_diseq_elim                       true
% 7.29/1.49  --brand_transform                       false
% 7.29/1.49  --non_eq_to_eq                          false
% 7.29/1.49  --prep_def_merge                        true
% 7.29/1.49  --prep_def_merge_prop_impl              false
% 7.29/1.49  --prep_def_merge_mbd                    true
% 7.29/1.49  --prep_def_merge_tr_red                 false
% 7.29/1.49  --prep_def_merge_tr_cl                  false
% 7.29/1.49  --smt_preprocessing                     true
% 7.29/1.49  --smt_ac_axioms                         fast
% 7.29/1.49  --preprocessed_out                      false
% 7.29/1.49  --preprocessed_stats                    false
% 7.29/1.49  
% 7.29/1.49  ------ Abstraction refinement Options
% 7.29/1.49  
% 7.29/1.49  --abstr_ref                             []
% 7.29/1.49  --abstr_ref_prep                        false
% 7.29/1.49  --abstr_ref_until_sat                   false
% 7.29/1.49  --abstr_ref_sig_restrict                funpre
% 7.29/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.29/1.49  --abstr_ref_under                       []
% 7.29/1.49  
% 7.29/1.49  ------ SAT Options
% 7.29/1.49  
% 7.29/1.49  --sat_mode                              false
% 7.29/1.49  --sat_fm_restart_options                ""
% 7.29/1.49  --sat_gr_def                            false
% 7.29/1.49  --sat_epr_types                         true
% 7.29/1.49  --sat_non_cyclic_types                  false
% 7.29/1.49  --sat_finite_models                     false
% 7.29/1.49  --sat_fm_lemmas                         false
% 7.29/1.49  --sat_fm_prep                           false
% 7.29/1.49  --sat_fm_uc_incr                        true
% 7.29/1.49  --sat_out_model                         small
% 7.29/1.49  --sat_out_clauses                       false
% 7.29/1.49  
% 7.29/1.49  ------ QBF Options
% 7.29/1.49  
% 7.29/1.49  --qbf_mode                              false
% 7.29/1.49  --qbf_elim_univ                         false
% 7.29/1.49  --qbf_dom_inst                          none
% 7.29/1.49  --qbf_dom_pre_inst                      false
% 7.29/1.49  --qbf_sk_in                             false
% 7.29/1.49  --qbf_pred_elim                         true
% 7.29/1.49  --qbf_split                             512
% 7.29/1.49  
% 7.29/1.49  ------ BMC1 Options
% 7.29/1.49  
% 7.29/1.49  --bmc1_incremental                      false
% 7.29/1.49  --bmc1_axioms                           reachable_all
% 7.29/1.49  --bmc1_min_bound                        0
% 7.29/1.49  --bmc1_max_bound                        -1
% 7.29/1.49  --bmc1_max_bound_default                -1
% 7.29/1.49  --bmc1_symbol_reachability              true
% 7.29/1.49  --bmc1_property_lemmas                  false
% 7.29/1.49  --bmc1_k_induction                      false
% 7.29/1.49  --bmc1_non_equiv_states                 false
% 7.29/1.49  --bmc1_deadlock                         false
% 7.29/1.49  --bmc1_ucm                              false
% 7.29/1.49  --bmc1_add_unsat_core                   none
% 7.29/1.49  --bmc1_unsat_core_children              false
% 7.29/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.29/1.49  --bmc1_out_stat                         full
% 7.29/1.49  --bmc1_ground_init                      false
% 7.29/1.49  --bmc1_pre_inst_next_state              false
% 7.29/1.49  --bmc1_pre_inst_state                   false
% 7.29/1.49  --bmc1_pre_inst_reach_state             false
% 7.29/1.49  --bmc1_out_unsat_core                   false
% 7.29/1.49  --bmc1_aig_witness_out                  false
% 7.29/1.49  --bmc1_verbose                          false
% 7.29/1.49  --bmc1_dump_clauses_tptp                false
% 7.29/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.29/1.49  --bmc1_dump_file                        -
% 7.29/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.29/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.29/1.49  --bmc1_ucm_extend_mode                  1
% 7.29/1.49  --bmc1_ucm_init_mode                    2
% 7.29/1.49  --bmc1_ucm_cone_mode                    none
% 7.29/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.29/1.49  --bmc1_ucm_relax_model                  4
% 7.29/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.29/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.29/1.49  --bmc1_ucm_layered_model                none
% 7.29/1.49  --bmc1_ucm_max_lemma_size               10
% 7.29/1.49  
% 7.29/1.49  ------ AIG Options
% 7.29/1.49  
% 7.29/1.49  --aig_mode                              false
% 7.29/1.49  
% 7.29/1.49  ------ Instantiation Options
% 7.29/1.49  
% 7.29/1.49  --instantiation_flag                    true
% 7.29/1.49  --inst_sos_flag                         false
% 7.29/1.49  --inst_sos_phase                        true
% 7.29/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.29/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.29/1.49  --inst_lit_sel_side                     num_symb
% 7.29/1.49  --inst_solver_per_active                1400
% 7.29/1.49  --inst_solver_calls_frac                1.
% 7.29/1.49  --inst_passive_queue_type               priority_queues
% 7.29/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.29/1.49  --inst_passive_queues_freq              [25;2]
% 7.29/1.49  --inst_dismatching                      true
% 7.29/1.49  --inst_eager_unprocessed_to_passive     true
% 7.29/1.49  --inst_prop_sim_given                   true
% 7.29/1.49  --inst_prop_sim_new                     false
% 7.29/1.49  --inst_subs_new                         false
% 7.29/1.49  --inst_eq_res_simp                      false
% 7.29/1.49  --inst_subs_given                       false
% 7.29/1.49  --inst_orphan_elimination               true
% 7.29/1.49  --inst_learning_loop_flag               true
% 7.29/1.49  --inst_learning_start                   3000
% 7.29/1.49  --inst_learning_factor                  2
% 7.29/1.49  --inst_start_prop_sim_after_learn       3
% 7.29/1.49  --inst_sel_renew                        solver
% 7.29/1.49  --inst_lit_activity_flag                true
% 7.29/1.49  --inst_restr_to_given                   false
% 7.29/1.49  --inst_activity_threshold               500
% 7.29/1.49  --inst_out_proof                        true
% 7.29/1.49  
% 7.29/1.49  ------ Resolution Options
% 7.29/1.49  
% 7.29/1.49  --resolution_flag                       true
% 7.29/1.49  --res_lit_sel                           adaptive
% 7.29/1.49  --res_lit_sel_side                      none
% 7.29/1.49  --res_ordering                          kbo
% 7.29/1.49  --res_to_prop_solver                    active
% 7.29/1.49  --res_prop_simpl_new                    false
% 7.29/1.49  --res_prop_simpl_given                  true
% 7.29/1.49  --res_passive_queue_type                priority_queues
% 7.29/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.29/1.49  --res_passive_queues_freq               [15;5]
% 7.29/1.49  --res_forward_subs                      full
% 7.29/1.49  --res_backward_subs                     full
% 7.29/1.49  --res_forward_subs_resolution           true
% 7.29/1.49  --res_backward_subs_resolution          true
% 7.29/1.49  --res_orphan_elimination                true
% 7.29/1.49  --res_time_limit                        2.
% 7.29/1.49  --res_out_proof                         true
% 7.29/1.49  
% 7.29/1.49  ------ Superposition Options
% 7.29/1.49  
% 7.29/1.49  --superposition_flag                    true
% 7.29/1.49  --sup_passive_queue_type                priority_queues
% 7.29/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.29/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.29/1.49  --demod_completeness_check              fast
% 7.29/1.49  --demod_use_ground                      true
% 7.29/1.49  --sup_to_prop_solver                    passive
% 7.29/1.49  --sup_prop_simpl_new                    true
% 7.29/1.49  --sup_prop_simpl_given                  true
% 7.29/1.49  --sup_fun_splitting                     false
% 7.29/1.49  --sup_smt_interval                      50000
% 7.29/1.49  
% 7.29/1.49  ------ Superposition Simplification Setup
% 7.29/1.49  
% 7.29/1.49  --sup_indices_passive                   []
% 7.29/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.29/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.49  --sup_full_bw                           [BwDemod]
% 7.29/1.49  --sup_immed_triv                        [TrivRules]
% 7.29/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.29/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.49  --sup_immed_bw_main                     []
% 7.29/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.29/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.49  
% 7.29/1.49  ------ Combination Options
% 7.29/1.49  
% 7.29/1.49  --comb_res_mult                         3
% 7.29/1.49  --comb_sup_mult                         2
% 7.29/1.49  --comb_inst_mult                        10
% 7.29/1.49  
% 7.29/1.49  ------ Debug Options
% 7.29/1.49  
% 7.29/1.49  --dbg_backtrace                         false
% 7.29/1.49  --dbg_dump_prop_clauses                 false
% 7.29/1.49  --dbg_dump_prop_clauses_file            -
% 7.29/1.49  --dbg_out_stat                          false
% 7.29/1.49  ------ Parsing...
% 7.29/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.29/1.49  ------ Proving...
% 7.29/1.49  ------ Problem Properties 
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  clauses                                 27
% 7.29/1.49  conjectures                             13
% 7.29/1.49  EPR                                     8
% 7.29/1.49  Horn                                    21
% 7.29/1.49  unary                                   14
% 7.29/1.49  binary                                  4
% 7.29/1.49  lits                                    115
% 7.29/1.49  lits eq                                 17
% 7.29/1.49  fd_pure                                 0
% 7.29/1.49  fd_pseudo                               0
% 7.29/1.49  fd_cond                                 0
% 7.29/1.49  fd_pseudo_cond                          0
% 7.29/1.49  AC symbols                              0
% 7.29/1.49  
% 7.29/1.49  ------ Schedule dynamic 5 is on 
% 7.29/1.49  
% 7.29/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  ------ 
% 7.29/1.49  Current options:
% 7.29/1.49  ------ 
% 7.29/1.49  
% 7.29/1.49  ------ Input Options
% 7.29/1.49  
% 7.29/1.49  --out_options                           all
% 7.29/1.49  --tptp_safe_out                         true
% 7.29/1.49  --problem_path                          ""
% 7.29/1.49  --include_path                          ""
% 7.29/1.49  --clausifier                            res/vclausify_rel
% 7.29/1.49  --clausifier_options                    --mode clausify
% 7.29/1.49  --stdin                                 false
% 7.29/1.49  --stats_out                             all
% 7.29/1.49  
% 7.29/1.49  ------ General Options
% 7.29/1.49  
% 7.29/1.49  --fof                                   false
% 7.29/1.49  --time_out_real                         305.
% 7.29/1.49  --time_out_virtual                      -1.
% 7.29/1.49  --symbol_type_check                     false
% 7.29/1.49  --clausify_out                          false
% 7.29/1.49  --sig_cnt_out                           false
% 7.29/1.49  --trig_cnt_out                          false
% 7.29/1.49  --trig_cnt_out_tolerance                1.
% 7.29/1.49  --trig_cnt_out_sk_spl                   false
% 7.29/1.49  --abstr_cl_out                          false
% 7.29/1.49  
% 7.29/1.49  ------ Global Options
% 7.29/1.49  
% 7.29/1.49  --schedule                              default
% 7.29/1.49  --add_important_lit                     false
% 7.29/1.49  --prop_solver_per_cl                    1000
% 7.29/1.49  --min_unsat_core                        false
% 7.29/1.49  --soft_assumptions                      false
% 7.29/1.49  --soft_lemma_size                       3
% 7.29/1.49  --prop_impl_unit_size                   0
% 7.29/1.49  --prop_impl_unit                        []
% 7.29/1.49  --share_sel_clauses                     true
% 7.29/1.49  --reset_solvers                         false
% 7.29/1.49  --bc_imp_inh                            [conj_cone]
% 7.29/1.49  --conj_cone_tolerance                   3.
% 7.29/1.49  --extra_neg_conj                        none
% 7.29/1.49  --large_theory_mode                     true
% 7.29/1.49  --prolific_symb_bound                   200
% 7.29/1.49  --lt_threshold                          2000
% 7.29/1.49  --clause_weak_htbl                      true
% 7.29/1.49  --gc_record_bc_elim                     false
% 7.29/1.49  
% 7.29/1.49  ------ Preprocessing Options
% 7.29/1.49  
% 7.29/1.49  --preprocessing_flag                    true
% 7.29/1.49  --time_out_prep_mult                    0.1
% 7.29/1.49  --splitting_mode                        input
% 7.29/1.49  --splitting_grd                         true
% 7.29/1.49  --splitting_cvd                         false
% 7.29/1.49  --splitting_cvd_svl                     false
% 7.29/1.49  --splitting_nvd                         32
% 7.29/1.49  --sub_typing                            true
% 7.29/1.49  --prep_gs_sim                           true
% 7.29/1.49  --prep_unflatten                        true
% 7.29/1.49  --prep_res_sim                          true
% 7.29/1.49  --prep_upred                            true
% 7.29/1.49  --prep_sem_filter                       exhaustive
% 7.29/1.49  --prep_sem_filter_out                   false
% 7.29/1.49  --pred_elim                             true
% 7.29/1.49  --res_sim_input                         true
% 7.29/1.49  --eq_ax_congr_red                       true
% 7.29/1.49  --pure_diseq_elim                       true
% 7.29/1.49  --brand_transform                       false
% 7.29/1.49  --non_eq_to_eq                          false
% 7.29/1.49  --prep_def_merge                        true
% 7.29/1.49  --prep_def_merge_prop_impl              false
% 7.29/1.49  --prep_def_merge_mbd                    true
% 7.29/1.49  --prep_def_merge_tr_red                 false
% 7.29/1.49  --prep_def_merge_tr_cl                  false
% 7.29/1.49  --smt_preprocessing                     true
% 7.29/1.49  --smt_ac_axioms                         fast
% 7.29/1.49  --preprocessed_out                      false
% 7.29/1.49  --preprocessed_stats                    false
% 7.29/1.49  
% 7.29/1.49  ------ Abstraction refinement Options
% 7.29/1.49  
% 7.29/1.49  --abstr_ref                             []
% 7.29/1.49  --abstr_ref_prep                        false
% 7.29/1.49  --abstr_ref_until_sat                   false
% 7.29/1.49  --abstr_ref_sig_restrict                funpre
% 7.29/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.29/1.49  --abstr_ref_under                       []
% 7.29/1.49  
% 7.29/1.49  ------ SAT Options
% 7.29/1.49  
% 7.29/1.49  --sat_mode                              false
% 7.29/1.49  --sat_fm_restart_options                ""
% 7.29/1.49  --sat_gr_def                            false
% 7.29/1.49  --sat_epr_types                         true
% 7.29/1.49  --sat_non_cyclic_types                  false
% 7.29/1.49  --sat_finite_models                     false
% 7.29/1.49  --sat_fm_lemmas                         false
% 7.29/1.49  --sat_fm_prep                           false
% 7.29/1.49  --sat_fm_uc_incr                        true
% 7.29/1.49  --sat_out_model                         small
% 7.29/1.49  --sat_out_clauses                       false
% 7.29/1.49  
% 7.29/1.49  ------ QBF Options
% 7.29/1.49  
% 7.29/1.49  --qbf_mode                              false
% 7.29/1.49  --qbf_elim_univ                         false
% 7.29/1.49  --qbf_dom_inst                          none
% 7.29/1.49  --qbf_dom_pre_inst                      false
% 7.29/1.49  --qbf_sk_in                             false
% 7.29/1.49  --qbf_pred_elim                         true
% 7.29/1.49  --qbf_split                             512
% 7.29/1.49  
% 7.29/1.49  ------ BMC1 Options
% 7.29/1.49  
% 7.29/1.49  --bmc1_incremental                      false
% 7.29/1.49  --bmc1_axioms                           reachable_all
% 7.29/1.49  --bmc1_min_bound                        0
% 7.29/1.49  --bmc1_max_bound                        -1
% 7.29/1.49  --bmc1_max_bound_default                -1
% 7.29/1.49  --bmc1_symbol_reachability              true
% 7.29/1.49  --bmc1_property_lemmas                  false
% 7.29/1.49  --bmc1_k_induction                      false
% 7.29/1.49  --bmc1_non_equiv_states                 false
% 7.29/1.49  --bmc1_deadlock                         false
% 7.29/1.49  --bmc1_ucm                              false
% 7.29/1.49  --bmc1_add_unsat_core                   none
% 7.29/1.49  --bmc1_unsat_core_children              false
% 7.29/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.29/1.49  --bmc1_out_stat                         full
% 7.29/1.49  --bmc1_ground_init                      false
% 7.29/1.49  --bmc1_pre_inst_next_state              false
% 7.29/1.49  --bmc1_pre_inst_state                   false
% 7.29/1.49  --bmc1_pre_inst_reach_state             false
% 7.29/1.49  --bmc1_out_unsat_core                   false
% 7.29/1.49  --bmc1_aig_witness_out                  false
% 7.29/1.49  --bmc1_verbose                          false
% 7.29/1.49  --bmc1_dump_clauses_tptp                false
% 7.29/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.29/1.49  --bmc1_dump_file                        -
% 7.29/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.29/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.29/1.49  --bmc1_ucm_extend_mode                  1
% 7.29/1.49  --bmc1_ucm_init_mode                    2
% 7.29/1.49  --bmc1_ucm_cone_mode                    none
% 7.29/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.29/1.49  --bmc1_ucm_relax_model                  4
% 7.29/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.29/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.29/1.49  --bmc1_ucm_layered_model                none
% 7.29/1.49  --bmc1_ucm_max_lemma_size               10
% 7.29/1.49  
% 7.29/1.49  ------ AIG Options
% 7.29/1.49  
% 7.29/1.49  --aig_mode                              false
% 7.29/1.49  
% 7.29/1.49  ------ Instantiation Options
% 7.29/1.49  
% 7.29/1.49  --instantiation_flag                    true
% 7.29/1.49  --inst_sos_flag                         false
% 7.29/1.49  --inst_sos_phase                        true
% 7.29/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.29/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.29/1.49  --inst_lit_sel_side                     none
% 7.29/1.49  --inst_solver_per_active                1400
% 7.29/1.49  --inst_solver_calls_frac                1.
% 7.29/1.49  --inst_passive_queue_type               priority_queues
% 7.29/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.29/1.49  --inst_passive_queues_freq              [25;2]
% 7.29/1.49  --inst_dismatching                      true
% 7.29/1.49  --inst_eager_unprocessed_to_passive     true
% 7.29/1.49  --inst_prop_sim_given                   true
% 7.29/1.49  --inst_prop_sim_new                     false
% 7.29/1.49  --inst_subs_new                         false
% 7.29/1.49  --inst_eq_res_simp                      false
% 7.29/1.49  --inst_subs_given                       false
% 7.29/1.49  --inst_orphan_elimination               true
% 7.29/1.49  --inst_learning_loop_flag               true
% 7.29/1.49  --inst_learning_start                   3000
% 7.29/1.49  --inst_learning_factor                  2
% 7.29/1.49  --inst_start_prop_sim_after_learn       3
% 7.29/1.49  --inst_sel_renew                        solver
% 7.29/1.49  --inst_lit_activity_flag                true
% 7.29/1.49  --inst_restr_to_given                   false
% 7.29/1.49  --inst_activity_threshold               500
% 7.29/1.49  --inst_out_proof                        true
% 7.29/1.49  
% 7.29/1.49  ------ Resolution Options
% 7.29/1.49  
% 7.29/1.49  --resolution_flag                       false
% 7.29/1.49  --res_lit_sel                           adaptive
% 7.29/1.49  --res_lit_sel_side                      none
% 7.29/1.49  --res_ordering                          kbo
% 7.29/1.49  --res_to_prop_solver                    active
% 7.29/1.49  --res_prop_simpl_new                    false
% 7.29/1.49  --res_prop_simpl_given                  true
% 7.29/1.49  --res_passive_queue_type                priority_queues
% 7.29/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.29/1.49  --res_passive_queues_freq               [15;5]
% 7.29/1.49  --res_forward_subs                      full
% 7.29/1.49  --res_backward_subs                     full
% 7.29/1.49  --res_forward_subs_resolution           true
% 7.29/1.49  --res_backward_subs_resolution          true
% 7.29/1.49  --res_orphan_elimination                true
% 7.29/1.49  --res_time_limit                        2.
% 7.29/1.49  --res_out_proof                         true
% 7.29/1.49  
% 7.29/1.49  ------ Superposition Options
% 7.29/1.49  
% 7.29/1.49  --superposition_flag                    true
% 7.29/1.49  --sup_passive_queue_type                priority_queues
% 7.29/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.29/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.29/1.49  --demod_completeness_check              fast
% 7.29/1.49  --demod_use_ground                      true
% 7.29/1.49  --sup_to_prop_solver                    passive
% 7.29/1.49  --sup_prop_simpl_new                    true
% 7.29/1.49  --sup_prop_simpl_given                  true
% 7.29/1.49  --sup_fun_splitting                     false
% 7.29/1.49  --sup_smt_interval                      50000
% 7.29/1.49  
% 7.29/1.49  ------ Superposition Simplification Setup
% 7.29/1.49  
% 7.29/1.49  --sup_indices_passive                   []
% 7.29/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.29/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.29/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.49  --sup_full_bw                           [BwDemod]
% 7.29/1.49  --sup_immed_triv                        [TrivRules]
% 7.29/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.29/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.49  --sup_immed_bw_main                     []
% 7.29/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.29/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.29/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.29/1.49  
% 7.29/1.49  ------ Combination Options
% 7.29/1.49  
% 7.29/1.49  --comb_res_mult                         3
% 7.29/1.49  --comb_sup_mult                         2
% 7.29/1.49  --comb_inst_mult                        10
% 7.29/1.49  
% 7.29/1.49  ------ Debug Options
% 7.29/1.49  
% 7.29/1.49  --dbg_backtrace                         false
% 7.29/1.49  --dbg_dump_prop_clauses                 false
% 7.29/1.49  --dbg_dump_prop_clauses_file            -
% 7.29/1.49  --dbg_out_stat                          false
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  ------ Proving...
% 7.29/1.49  
% 7.29/1.49  
% 7.29/1.49  % SZS status Theorem for theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.29/1.49  
% 7.29/1.49  fof(f12,conjecture,(
% 7.29/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f13,negated_conjecture,(
% 7.29/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 7.29/1.49    inference(negated_conjecture,[],[f12])).
% 7.29/1.49  
% 7.29/1.49  fof(f30,plain,(
% 7.29/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.29/1.49    inference(ennf_transformation,[],[f13])).
% 7.29/1.49  
% 7.29/1.49  fof(f31,plain,(
% 7.29/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 7.29/1.49    inference(flattening,[],[f30])).
% 7.29/1.49  
% 7.29/1.49  fof(f41,plain,(
% 7.29/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f40,plain,(
% 7.29/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f39,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f38,plain,(
% 7.29/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f37,plain,(
% 7.29/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f36,plain,(
% 7.29/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 7.29/1.49    introduced(choice_axiom,[])).
% 7.29/1.49  
% 7.29/1.49  fof(f42,plain,(
% 7.29/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 7.29/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f31,f41,f40,f39,f38,f37,f36])).
% 7.29/1.49  
% 7.29/1.49  fof(f65,plain,(
% 7.29/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f3,axiom,(
% 7.29/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f15,plain,(
% 7.29/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f3])).
% 7.29/1.49  
% 7.29/1.49  fof(f46,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.29/1.49    inference(cnf_transformation,[],[f15])).
% 7.29/1.49  
% 7.29/1.49  fof(f69,plain,(
% 7.29/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f9,axiom,(
% 7.29/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f24,plain,(
% 7.29/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 7.29/1.49    inference(ennf_transformation,[],[f9])).
% 7.29/1.49  
% 7.29/1.49  fof(f25,plain,(
% 7.29/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 7.29/1.49    inference(flattening,[],[f24])).
% 7.29/1.49  
% 7.29/1.49  fof(f53,plain,(
% 7.29/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f25])).
% 7.29/1.49  
% 7.29/1.49  fof(f67,plain,(
% 7.29/1.49    v1_funct_1(sK4)),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f72,plain,(
% 7.29/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f70,plain,(
% 7.29/1.49    v1_funct_1(sK5)),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f10,axiom,(
% 7.29/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f26,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.29/1.49    inference(ennf_transformation,[],[f10])).
% 7.29/1.49  
% 7.29/1.49  fof(f27,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.29/1.49    inference(flattening,[],[f26])).
% 7.29/1.49  
% 7.29/1.49  fof(f34,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.29/1.49    inference(nnf_transformation,[],[f27])).
% 7.29/1.49  
% 7.29/1.49  fof(f35,plain,(
% 7.29/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 7.29/1.49    inference(flattening,[],[f34])).
% 7.29/1.49  
% 7.29/1.49  fof(f55,plain,(
% 7.29/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f35])).
% 7.29/1.49  
% 7.29/1.49  fof(f76,plain,(
% 7.29/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.29/1.49    inference(equality_resolution,[],[f55])).
% 7.29/1.49  
% 7.29/1.49  fof(f11,axiom,(
% 7.29/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f28,plain,(
% 7.29/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f11])).
% 7.29/1.49  
% 7.29/1.49  fof(f29,plain,(
% 7.29/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.29/1.49    inference(flattening,[],[f28])).
% 7.29/1.49  
% 7.29/1.49  fof(f57,plain,(
% 7.29/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f29])).
% 7.29/1.49  
% 7.29/1.49  fof(f58,plain,(
% 7.29/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f29])).
% 7.29/1.49  
% 7.29/1.49  fof(f59,plain,(
% 7.29/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f29])).
% 7.29/1.49  
% 7.29/1.49  fof(f61,plain,(
% 7.29/1.49    ~v1_xboole_0(sK1)),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f64,plain,(
% 7.29/1.49    ~v1_xboole_0(sK3)),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f71,plain,(
% 7.29/1.49    v1_funct_2(sK5,sK3,sK1)),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f62,plain,(
% 7.29/1.49    ~v1_xboole_0(sK2)),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f68,plain,(
% 7.29/1.49    v1_funct_2(sK4,sK2,sK1)),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f1,axiom,(
% 7.29/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f32,plain,(
% 7.29/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 7.29/1.49    inference(nnf_transformation,[],[f1])).
% 7.29/1.49  
% 7.29/1.49  fof(f43,plain,(
% 7.29/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f32])).
% 7.29/1.49  
% 7.29/1.49  fof(f6,axiom,(
% 7.29/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f20,plain,(
% 7.29/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 7.29/1.49    inference(ennf_transformation,[],[f6])).
% 7.29/1.49  
% 7.29/1.49  fof(f21,plain,(
% 7.29/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.29/1.49    inference(flattening,[],[f20])).
% 7.29/1.49  
% 7.29/1.49  fof(f33,plain,(
% 7.29/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 7.29/1.49    inference(nnf_transformation,[],[f21])).
% 7.29/1.49  
% 7.29/1.49  fof(f49,plain,(
% 7.29/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f33])).
% 7.29/1.49  
% 7.29/1.49  fof(f66,plain,(
% 7.29/1.49    r1_subset_1(sK2,sK3)),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f8,axiom,(
% 7.29/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f14,plain,(
% 7.29/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.29/1.49    inference(pure_predicate_removal,[],[f8])).
% 7.29/1.49  
% 7.29/1.49  fof(f23,plain,(
% 7.29/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.29/1.49    inference(ennf_transformation,[],[f14])).
% 7.29/1.49  
% 7.29/1.49  fof(f52,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.29/1.49    inference(cnf_transformation,[],[f23])).
% 7.29/1.49  
% 7.29/1.49  fof(f5,axiom,(
% 7.29/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f18,plain,(
% 7.29/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.29/1.49    inference(ennf_transformation,[],[f5])).
% 7.29/1.49  
% 7.29/1.49  fof(f19,plain,(
% 7.29/1.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.29/1.49    inference(flattening,[],[f18])).
% 7.29/1.49  
% 7.29/1.49  fof(f48,plain,(
% 7.29/1.49    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f19])).
% 7.29/1.49  
% 7.29/1.49  fof(f7,axiom,(
% 7.29/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f22,plain,(
% 7.29/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.29/1.49    inference(ennf_transformation,[],[f7])).
% 7.29/1.49  
% 7.29/1.49  fof(f51,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.29/1.49    inference(cnf_transformation,[],[f22])).
% 7.29/1.49  
% 7.29/1.49  fof(f2,axiom,(
% 7.29/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f45,plain,(
% 7.29/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.29/1.49    inference(cnf_transformation,[],[f2])).
% 7.29/1.49  
% 7.29/1.49  fof(f44,plain,(
% 7.29/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.29/1.49    inference(cnf_transformation,[],[f32])).
% 7.29/1.49  
% 7.29/1.49  fof(f4,axiom,(
% 7.29/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 7.29/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.29/1.49  
% 7.29/1.49  fof(f16,plain,(
% 7.29/1.49    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 7.29/1.49    inference(ennf_transformation,[],[f4])).
% 7.29/1.49  
% 7.29/1.49  fof(f17,plain,(
% 7.29/1.49    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 7.29/1.49    inference(flattening,[],[f16])).
% 7.29/1.49  
% 7.29/1.49  fof(f47,plain,(
% 7.29/1.49    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f17])).
% 7.29/1.49  
% 7.29/1.49  fof(f60,plain,(
% 7.29/1.49    ~v1_xboole_0(sK0)),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f63,plain,(
% 7.29/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f73,plain,(
% 7.29/1.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 7.29/1.49    inference(cnf_transformation,[],[f42])).
% 7.29/1.49  
% 7.29/1.49  fof(f54,plain,(
% 7.29/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.29/1.49    inference(cnf_transformation,[],[f35])).
% 7.29/1.49  
% 7.29/1.49  fof(f77,plain,(
% 7.29/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 7.29/1.49    inference(equality_resolution,[],[f54])).
% 7.29/1.49  
% 7.29/1.49  cnf(c_25,negated_conjecture,
% 7.29/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.29/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_718,negated_conjecture,
% 7.29/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1189,plain,
% 7.29/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_3,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.29/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_732,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 7.29/1.49      | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1176,plain,
% 7.29/1.49      ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
% 7.29/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2353,plain,
% 7.29/1.49      ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1189,c_1176]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_21,negated_conjecture,
% 7.29/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.29/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_721,negated_conjecture,
% 7.29/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_21]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1186,plain,
% 7.29/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_10,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.49      | ~ v1_funct_1(X0)
% 7.29/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 7.29/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_730,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.29/1.49      | ~ v1_funct_1(X0_51)
% 7.29/1.49      | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1178,plain,
% 7.29/1.49      ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
% 7.29/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.29/1.49      | v1_funct_1(X2_51) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2410,plain,
% 7.29/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
% 7.29/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1186,c_1178]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_23,negated_conjecture,
% 7.29/1.49      ( v1_funct_1(sK4) ),
% 7.29/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1564,plain,
% 7.29/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.29/1.49      | ~ v1_funct_1(sK4)
% 7.29/1.49      | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_730]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1732,plain,
% 7.29/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 7.29/1.49      | ~ v1_funct_1(sK4)
% 7.29/1.49      | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_1564]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2756,plain,
% 7.29/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_2410,c_23,c_21,c_1732]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_18,negated_conjecture,
% 7.29/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.29/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_724,negated_conjecture,
% 7.29/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1183,plain,
% 7.29/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2409,plain,
% 7.29/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
% 7.29/1.49      | v1_funct_1(sK5) != iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1183,c_1178]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_20,negated_conjecture,
% 7.29/1.49      ( v1_funct_1(sK5) ),
% 7.29/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1559,plain,
% 7.29/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 7.29/1.49      | ~ v1_funct_1(sK5)
% 7.29/1.49      | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_730]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1727,plain,
% 7.29/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 7.29/1.49      | ~ v1_funct_1(sK5)
% 7.29/1.49      | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 7.29/1.49      inference(instantiation,[status(thm)],[c_1559]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2751,plain,
% 7.29/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_2409,c_20,c_18,c_1727]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_12,plain,
% 7.29/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.29/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.29/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.29/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.29/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.29/1.49      | ~ v1_funct_1(X0)
% 7.29/1.49      | ~ v1_funct_1(X3)
% 7.29/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.29/1.49      | v1_xboole_0(X5)
% 7.29/1.49      | v1_xboole_0(X2)
% 7.29/1.49      | v1_xboole_0(X4)
% 7.29/1.49      | v1_xboole_0(X1)
% 7.29/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.29/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.29/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_16,plain,
% 7.29/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.29/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.29/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.29/1.49      | ~ v1_funct_1(X0)
% 7.29/1.49      | ~ v1_funct_1(X3)
% 7.29/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.29/1.49      | v1_xboole_0(X5)
% 7.29/1.49      | v1_xboole_0(X2)
% 7.29/1.49      | v1_xboole_0(X4)
% 7.29/1.49      | v1_xboole_0(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_15,plain,
% 7.29/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.29/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.29/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.29/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.29/1.49      | ~ v1_funct_1(X0)
% 7.29/1.49      | ~ v1_funct_1(X3)
% 7.29/1.49      | v1_xboole_0(X5)
% 7.29/1.49      | v1_xboole_0(X2)
% 7.29/1.49      | v1_xboole_0(X4)
% 7.29/1.49      | v1_xboole_0(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_14,plain,
% 7.29/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.29/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.29/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.29/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.29/1.49      | ~ v1_funct_1(X0)
% 7.29/1.49      | ~ v1_funct_1(X3)
% 7.29/1.49      | v1_xboole_0(X5)
% 7.29/1.49      | v1_xboole_0(X2)
% 7.29/1.49      | v1_xboole_0(X4)
% 7.29/1.49      | v1_xboole_0(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_173,plain,
% 7.29/1.49      ( ~ v1_funct_1(X3)
% 7.29/1.49      | ~ v1_funct_1(X0)
% 7.29/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.29/1.49      | ~ v1_funct_2(X0,X1,X2)
% 7.29/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.29/1.49      | v1_xboole_0(X5)
% 7.29/1.49      | v1_xboole_0(X2)
% 7.29/1.49      | v1_xboole_0(X4)
% 7.29/1.49      | v1_xboole_0(X1)
% 7.29/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.29/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_12,c_16,c_15,c_14]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_174,plain,
% 7.29/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.29/1.49      | ~ v1_funct_2(X3,X4,X2)
% 7.29/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.29/1.49      | ~ v1_funct_1(X0)
% 7.29/1.49      | ~ v1_funct_1(X3)
% 7.29/1.49      | v1_xboole_0(X1)
% 7.29/1.49      | v1_xboole_0(X2)
% 7.29/1.49      | v1_xboole_0(X4)
% 7.29/1.49      | v1_xboole_0(X5)
% 7.29/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.29/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_173]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_711,plain,
% 7.29/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 7.29/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 7.29/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 7.29/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 7.29/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.29/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.29/1.49      | ~ v1_funct_1(X0_51)
% 7.29/1.49      | ~ v1_funct_1(X3_51)
% 7.29/1.49      | v1_xboole_0(X1_51)
% 7.29/1.49      | v1_xboole_0(X2_51)
% 7.29/1.49      | v1_xboole_0(X4_51)
% 7.29/1.49      | v1_xboole_0(X5_51)
% 7.29/1.49      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 7.29/1.49      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X1_51) = X0_51 ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_174]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1196,plain,
% 7.29/1.49      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 7.29/1.49      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X0_51) = X2_51
% 7.29/1.49      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 7.29/1.49      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 7.29/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.29/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 7.29/1.49      | v1_funct_1(X2_51) != iProver_top
% 7.29/1.49      | v1_funct_1(X5_51) != iProver_top
% 7.29/1.49      | v1_xboole_0(X3_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X4_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5607,plain,
% 7.29/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.29/1.49      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.29/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.29/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.29/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.29/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.29/1.49      | v1_funct_1(sK5) != iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.29/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_2751,c_1196]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_29,negated_conjecture,
% 7.29/1.49      ( ~ v1_xboole_0(sK1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_32,plain,
% 7.29/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_26,negated_conjecture,
% 7.29/1.49      ( ~ v1_xboole_0(sK3) ),
% 7.29/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_35,plain,
% 7.29/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_41,plain,
% 7.29/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_19,negated_conjecture,
% 7.29/1.49      ( v1_funct_2(sK5,sK3,sK1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_42,plain,
% 7.29/1.49      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_43,plain,
% 7.29/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17815,plain,
% 7.29/1.49      ( v1_funct_1(X1_51) != iProver_top
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.29/1.49      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.29/1.49      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.29/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X2_51) = iProver_top ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_5607,c_32,c_35,c_41,c_42,c_43]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17816,plain,
% 7.29/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.29/1.49      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),sK3) = sK5
% 7.29/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.29/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.49      | v1_funct_1(X1_51) != iProver_top
% 7.29/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_17815]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17831,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.29/1.49      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.29/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.29/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | v1_funct_1(sK4) != iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_2756,c_17816]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_28,negated_conjecture,
% 7.29/1.49      ( ~ v1_xboole_0(sK2) ),
% 7.29/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_33,plain,
% 7.29/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_38,plain,
% 7.29/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_22,negated_conjecture,
% 7.29/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_39,plain,
% 7.29/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_40,plain,
% 7.29/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17965,plain,
% 7.29/1.49      ( v1_xboole_0(X0_51) = iProver_top
% 7.29/1.49      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.29/1.49      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_17831,c_33,c_38,c_39,c_40]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17966,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.29/1.49      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_17965]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17976,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.29/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_2353,c_17966]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1,plain,
% 7.29/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.29/1.49      inference(cnf_transformation,[],[f43]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_224,plain,
% 7.29/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.29/1.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_7,plain,
% 7.29/1.49      ( ~ r1_subset_1(X0,X1)
% 7.29/1.49      | r1_xboole_0(X0,X1)
% 7.29/1.49      | v1_xboole_0(X0)
% 7.29/1.49      | v1_xboole_0(X1) ),
% 7.29/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_24,negated_conjecture,
% 7.29/1.49      ( r1_subset_1(sK2,sK3) ),
% 7.29/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_435,plain,
% 7.29/1.49      ( r1_xboole_0(X0,X1)
% 7.29/1.49      | v1_xboole_0(X0)
% 7.29/1.49      | v1_xboole_0(X1)
% 7.29/1.49      | sK3 != X1
% 7.29/1.49      | sK2 != X0 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_7,c_24]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_436,plain,
% 7.29/1.49      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_435]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_438,plain,
% 7.29/1.49      ( r1_xboole_0(sK2,sK3) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_436,c_28,c_26]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_475,plain,
% 7.29/1.49      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 7.29/1.49      inference(resolution_lifted,[status(thm)],[c_224,c_438]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_476,plain,
% 7.29/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.29/1.49      inference(unflattening,[status(thm)],[c_475]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_707,plain,
% 7.29/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_476]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_9,plain,
% 7.29/1.49      ( v4_relat_1(X0,X1)
% 7.29/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.29/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_5,plain,
% 7.29/1.49      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.29/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_396,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.49      | ~ v1_relat_1(X0)
% 7.29/1.49      | k7_relat_1(X0,X1) = X0 ),
% 7.29/1.49      inference(resolution,[status(thm)],[c_9,c_5]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_8,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.49      | v1_relat_1(X0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_400,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.49      | k7_relat_1(X0,X1) = X0 ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_396,c_9,c_8,c_5]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_710,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.29/1.49      | k7_relat_1(X0_51,X1_51) = X0_51 ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_400]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1197,plain,
% 7.29/1.49      ( k7_relat_1(X0_51,X1_51) = X0_51
% 7.29/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2864,plain,
% 7.29/1.49      ( k7_relat_1(sK5,sK3) = sK5 ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1183,c_1197]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_731,plain,
% 7.29/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.29/1.49      | v1_relat_1(X0_51) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_8]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1177,plain,
% 7.29/1.49      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 7.29/1.49      | v1_relat_1(X0_51) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2139,plain,
% 7.29/1.49      ( v1_relat_1(sK5) = iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1183,c_1177]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2,plain,
% 7.29/1.49      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.29/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_733,plain,
% 7.29/1.49      ( k3_xboole_0(X0_51,k1_xboole_0) = k1_xboole_0 ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_2]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_0,plain,
% 7.29/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.29/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_222,plain,
% 7.29/1.49      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.29/1.49      inference(prop_impl,[status(thm)],[c_0]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_4,plain,
% 7.29/1.49      ( ~ r1_xboole_0(X0,X1)
% 7.29/1.49      | ~ v1_relat_1(X2)
% 7.29/1.49      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 7.29/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_448,plain,
% 7.29/1.49      ( ~ v1_relat_1(X0)
% 7.29/1.49      | k7_relat_1(k7_relat_1(X0,X1),X2) = k1_xboole_0
% 7.29/1.49      | k3_xboole_0(X1,X2) != k1_xboole_0 ),
% 7.29/1.49      inference(resolution,[status(thm)],[c_222,c_4]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_709,plain,
% 7.29/1.49      ( ~ v1_relat_1(X0_51)
% 7.29/1.49      | k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k1_xboole_0
% 7.29/1.49      | k3_xboole_0(X1_51,X2_51) != k1_xboole_0 ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_448]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1198,plain,
% 7.29/1.49      ( k7_relat_1(k7_relat_1(X0_51,X1_51),X2_51) = k1_xboole_0
% 7.29/1.49      | k3_xboole_0(X1_51,X2_51) != k1_xboole_0
% 7.29/1.49      | v1_relat_1(X0_51) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_3472,plain,
% 7.29/1.49      ( k7_relat_1(k7_relat_1(X0_51,X1_51),k1_xboole_0) = k1_xboole_0
% 7.29/1.49      | v1_relat_1(X0_51) != iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_733,c_1198]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_3810,plain,
% 7.29/1.49      ( k7_relat_1(k7_relat_1(sK5,X0_51),k1_xboole_0) = k1_xboole_0 ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_2139,c_3472]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_3878,plain,
% 7.29/1.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_2864,c_3810]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17977,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.29/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.49      inference(light_normalisation,[status(thm)],[c_17976,c_707,c_3878]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_728,plain,
% 7.29/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 7.29/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 7.29/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 7.29/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 7.29/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.29/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.29/1.49      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51)))
% 7.29/1.49      | ~ v1_funct_1(X0_51)
% 7.29/1.49      | ~ v1_funct_1(X3_51)
% 7.29/1.49      | v1_xboole_0(X1_51)
% 7.29/1.49      | v1_xboole_0(X2_51)
% 7.29/1.49      | v1_xboole_0(X4_51)
% 7.29/1.49      | v1_xboole_0(X5_51) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1180,plain,
% 7.29/1.49      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 7.29/1.49      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 7.29/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 7.29/1.49      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 7.29/1.49      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51))) = iProver_top
% 7.29/1.49      | v1_funct_1(X0_51) != iProver_top
% 7.29/1.49      | v1_funct_1(X3_51) != iProver_top
% 7.29/1.49      | v1_xboole_0(X5_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X4_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X1_51) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2514,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
% 7.29/1.49      | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
% 7.29/1.49      | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 7.29/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 7.29/1.49      | v1_funct_1(X5_51) != iProver_top
% 7.29/1.49      | v1_funct_1(X4_51) != iProver_top
% 7.29/1.49      | v1_funct_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51)) != iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X3_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X2_51) = iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1180,c_1178]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_726,plain,
% 7.29/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 7.29/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 7.29/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 7.29/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 7.29/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.29/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.29/1.49      | ~ v1_funct_1(X0_51)
% 7.29/1.49      | ~ v1_funct_1(X3_51)
% 7.29/1.49      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51))
% 7.29/1.49      | v1_xboole_0(X1_51)
% 7.29/1.49      | v1_xboole_0(X2_51)
% 7.29/1.49      | v1_xboole_0(X4_51)
% 7.29/1.49      | v1_xboole_0(X5_51) ),
% 7.29/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_1182,plain,
% 7.29/1.49      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 7.29/1.49      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 7.29/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 7.29/1.49      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 7.29/1.49      | v1_funct_1(X0_51) != iProver_top
% 7.29/1.49      | v1_funct_1(X3_51) != iProver_top
% 7.29/1.49      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51)) = iProver_top
% 7.29/1.49      | v1_xboole_0(X5_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X4_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X1_51) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_8671,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
% 7.29/1.49      | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
% 7.29/1.49      | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
% 7.29/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 7.29/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 7.29/1.49      | v1_funct_1(X5_51) != iProver_top
% 7.29/1.49      | v1_funct_1(X4_51) != iProver_top
% 7.29/1.49      | v1_xboole_0(X2_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X3_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.49      inference(forward_subsumption_resolution,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_2514,c_1182]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_8675,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 7.29/1.49      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 7.29/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | v1_funct_1(X2_51) != iProver_top
% 7.29/1.49      | v1_funct_1(sK5) != iProver_top
% 7.29/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(sK1) = iProver_top
% 7.29/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1183,c_8671]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_9290,plain,
% 7.29/1.49      ( v1_funct_1(X2_51) != iProver_top
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 7.29/1.49      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 7.29/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_8675,c_32,c_35,c_41,c_42]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_9291,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 7.29/1.49      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 7.29/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | v1_funct_1(X2_51) != iProver_top
% 7.29/1.49      | v1_xboole_0(X1_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_9290]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_9305,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 7.29/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | v1_funct_1(sK4) != iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1186,c_9291]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_9891,plain,
% 7.29/1.49      ( v1_xboole_0(X0_51) = iProver_top
% 7.29/1.49      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_9305,c_33,c_38,c_39]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_9892,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.49      inference(renaming,[status(thm)],[c_9891]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_9901,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51)
% 7.29/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1189,c_9892]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_30,negated_conjecture,
% 7.29/1.49      ( ~ v1_xboole_0(sK0) ),
% 7.29/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_31,plain,
% 7.29/1.49      ( v1_xboole_0(sK0) != iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_27,negated_conjecture,
% 7.29/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 7.29/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_34,plain,
% 7.29/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.29/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_9943,plain,
% 7.29/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) ),
% 7.29/1.49      inference(global_propositional_subsumption,
% 7.29/1.49                [status(thm)],
% 7.29/1.49                [c_9901,c_31,c_34]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_17978,plain,
% 7.29/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.29/1.49      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.29/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.49      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.49      inference(demodulation,[status(thm)],[c_17977,c_2353,c_9943]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2865,plain,
% 7.29/1.49      ( k7_relat_1(sK4,sK2) = sK4 ),
% 7.29/1.49      inference(superposition,[status(thm)],[c_1186,c_1197]) ).
% 7.29/1.49  
% 7.29/1.49  cnf(c_2140,plain,
% 7.29/1.49      ( v1_relat_1(sK4) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_1186,c_1177]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_3811,plain,
% 7.29/1.50      ( k7_relat_1(k7_relat_1(sK4,X0_51),k1_xboole_0) = k1_xboole_0 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2140,c_3472]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_3933,plain,
% 7.29/1.50      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2865,c_3811]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_17979,plain,
% 7.29/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.29/1.50      | k1_xboole_0 != k1_xboole_0
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.50      inference(light_normalisation,[status(thm)],[c_17978,c_707,c_3933]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_17980,plain,
% 7.29/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.50      inference(equality_resolution_simp,[status(thm)],[c_17979]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_17,negated_conjecture,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.29/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.29/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_725,negated_conjecture,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.29/1.50      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 7.29/1.50      inference(subtyping,[status(esa)],[c_17]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_2645,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.29/1.50      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 7.29/1.50      inference(demodulation,[status(thm)],[c_2353,c_725]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_2646,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.29/1.50      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 7.29/1.50      inference(light_normalisation,[status(thm)],[c_2645,c_707]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_2857,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.29/1.50      | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) ),
% 7.29/1.50      inference(demodulation,[status(thm)],[c_2646,c_2751,c_2756]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_3880,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.29/1.50      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 7.29/1.50      inference(demodulation,[status(thm)],[c_3878,c_2857]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_17581,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_3880,c_3933]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_17582,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 7.29/1.50      inference(renaming,[status(thm)],[c_17581]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_13,plain,
% 7.29/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.29/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.29/1.50      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 7.29/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.29/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.29/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.29/1.50      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 7.29/1.50      | ~ v1_funct_1(X0)
% 7.29/1.50      | ~ v1_funct_1(X3)
% 7.29/1.50      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 7.29/1.50      | v1_xboole_0(X5)
% 7.29/1.50      | v1_xboole_0(X2)
% 7.29/1.50      | v1_xboole_0(X4)
% 7.29/1.50      | v1_xboole_0(X1)
% 7.29/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.29/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.29/1.50      inference(cnf_transformation,[],[f77]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_166,plain,
% 7.29/1.50      ( ~ v1_funct_1(X3)
% 7.29/1.50      | ~ v1_funct_1(X0)
% 7.29/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.29/1.50      | ~ v1_funct_2(X0,X1,X2)
% 7.29/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.29/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.29/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.29/1.50      | v1_xboole_0(X5)
% 7.29/1.50      | v1_xboole_0(X2)
% 7.29/1.50      | v1_xboole_0(X4)
% 7.29/1.50      | v1_xboole_0(X1)
% 7.29/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.29/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_13,c_16,c_15,c_14]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_167,plain,
% 7.29/1.50      ( ~ v1_funct_2(X0,X1,X2)
% 7.29/1.50      | ~ v1_funct_2(X3,X4,X2)
% 7.29/1.50      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 7.29/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 7.29/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.29/1.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.29/1.50      | ~ v1_funct_1(X0)
% 7.29/1.50      | ~ v1_funct_1(X3)
% 7.29/1.50      | v1_xboole_0(X1)
% 7.29/1.50      | v1_xboole_0(X2)
% 7.29/1.50      | v1_xboole_0(X4)
% 7.29/1.50      | v1_xboole_0(X5)
% 7.29/1.50      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 7.29/1.50      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 7.29/1.50      inference(renaming,[status(thm)],[c_166]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_712,plain,
% 7.29/1.50      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 7.29/1.50      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 7.29/1.50      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 7.29/1.50      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 7.29/1.50      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 7.29/1.50      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 7.29/1.50      | ~ v1_funct_1(X0_51)
% 7.29/1.50      | ~ v1_funct_1(X3_51)
% 7.29/1.50      | v1_xboole_0(X1_51)
% 7.29/1.50      | v1_xboole_0(X2_51)
% 7.29/1.50      | v1_xboole_0(X4_51)
% 7.29/1.50      | v1_xboole_0(X5_51)
% 7.29/1.50      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 7.29/1.50      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X4_51) = X3_51 ),
% 7.29/1.50      inference(subtyping,[status(esa)],[c_167]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_1195,plain,
% 7.29/1.50      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 7.29/1.50      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X4_51) = X5_51
% 7.29/1.50      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 7.29/1.50      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 7.29/1.50      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.29/1.50      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 7.29/1.50      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 7.29/1.50      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 7.29/1.50      | v1_funct_1(X2_51) != iProver_top
% 7.29/1.50      | v1_funct_1(X5_51) != iProver_top
% 7.29/1.50      | v1_xboole_0(X3_51) = iProver_top
% 7.29/1.50      | v1_xboole_0(X1_51) = iProver_top
% 7.29/1.50      | v1_xboole_0(X4_51) = iProver_top
% 7.29/1.50      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_4164,plain,
% 7.29/1.50      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.29/1.50      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.29/1.50      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.29/1.50      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.50      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.50      | v1_funct_1(X1_51) != iProver_top
% 7.29/1.50      | v1_funct_1(sK5) != iProver_top
% 7.29/1.50      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.50      | v1_xboole_0(X2_51) = iProver_top
% 7.29/1.50      | v1_xboole_0(sK1) = iProver_top
% 7.29/1.50      | v1_xboole_0(sK3) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2751,c_1195]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11963,plain,
% 7.29/1.50      ( v1_funct_1(X1_51) != iProver_top
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.50      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.29/1.50      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.29/1.50      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.29/1.50      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.50      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.29/1.50      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.50      | v1_xboole_0(X2_51) = iProver_top ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_4164,c_32,c_35,c_41,c_42,c_43]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11964,plain,
% 7.29/1.50      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(X2_51,X0_51,sK3))
% 7.29/1.50      | k2_partfun1(k4_subset_1(X2_51,X0_51,sK3),sK1,k1_tmap_1(X2_51,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.29/1.50      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.50      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X2_51)) != iProver_top
% 7.29/1.50      | v1_funct_1(X1_51) != iProver_top
% 7.29/1.50      | v1_xboole_0(X2_51) = iProver_top
% 7.29/1.50      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.50      inference(renaming,[status(thm)],[c_11963]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11984,plain,
% 7.29/1.50      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0_51,sK3))
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.29/1.50      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_funct_1(X1_51) != iProver_top
% 7.29/1.50      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2353,c_11964]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11994,plain,
% 7.29/1.50      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.29/1.50      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_funct_1(X1_51) != iProver_top
% 7.29/1.50      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.50      inference(light_normalisation,[status(thm)],[c_11984,c_2353]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_36,plain,
% 7.29/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.29/1.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12454,plain,
% 7.29/1.50      ( v1_xboole_0(X0_51) = iProver_top
% 7.29/1.50      | v1_funct_1(X1_51) != iProver_top
% 7.29/1.50      | k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.29/1.50      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_11994,c_31,c_36]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12455,plain,
% 7.29/1.50      ( k2_partfun1(X0_51,sK1,X1_51,k3_xboole_0(X0_51,sK3)) != k7_relat_1(sK5,k3_xboole_0(X0_51,sK3))
% 7.29/1.50      | k2_partfun1(k4_subset_1(sK0,X0_51,sK3),sK1,k1_tmap_1(sK0,sK1,X0_51,sK3,X1_51,sK5),X0_51) = X1_51
% 7.29/1.50      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(X0_51,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_funct_1(X1_51) != iProver_top
% 7.29/1.50      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.50      inference(renaming,[status(thm)],[c_12454]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12468,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.29/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_funct_1(sK4) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2756,c_12455]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12552,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | k1_xboole_0 != k1_xboole_0
% 7.29/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_funct_1(sK4) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.29/1.50      inference(light_normalisation,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_12468,c_707,c_3878,c_3933]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12553,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_funct_1(sK4) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.29/1.50      inference(equality_resolution_simp,[status(thm)],[c_12552]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12554,plain,
% 7.29/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_funct_1(sK4) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.29/1.50      inference(demodulation,[status(thm)],[c_12553,c_9943]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_11979,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.29/1.50      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 7.29/1.50      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.50      | v1_funct_1(sK4) != iProver_top
% 7.29/1.50      | v1_xboole_0(X0_51) = iProver_top
% 7.29/1.50      | v1_xboole_0(sK2) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2756,c_11964]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12436,plain,
% 7.29/1.50      ( v1_xboole_0(X0_51) = iProver_top
% 7.29/1.50      | k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_11979,c_33,c_38,c_39,c_40]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12437,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | k7_relat_1(sK5,k9_subset_1(X0_51,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(X0_51,sK2,sK3))
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 7.29/1.50      | v1_xboole_0(X0_51) = iProver_top ),
% 7.29/1.50      inference(renaming,[status(thm)],[c_12436]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12447,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.50      inference(superposition,[status(thm)],[c_2353,c_12437]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12448,plain,
% 7.29/1.50      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k1_xboole_0
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.50      inference(light_normalisation,[status(thm)],[c_12447,c_707,c_3878]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12449,plain,
% 7.29/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | k7_relat_1(sK4,k3_xboole_0(sK2,sK3)) != k1_xboole_0
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.50      inference(demodulation,[status(thm)],[c_12448,c_2353,c_9943]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12450,plain,
% 7.29/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | k1_xboole_0 != k1_xboole_0
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.50      inference(light_normalisation,[status(thm)],[c_12449,c_707,c_3933]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12451,plain,
% 7.29/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 7.29/1.50      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 7.29/1.50      | v1_xboole_0(sK0) = iProver_top ),
% 7.29/1.50      inference(equality_resolution_simp,[status(thm)],[c_12450]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_12642,plain,
% 7.29/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4 ),
% 7.29/1.50      inference(global_propositional_subsumption,
% 7.29/1.50                [status(thm)],
% 7.29/1.50                [c_12554,c_31,c_34,c_36,c_12451]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_17583,plain,
% 7.29/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 7.29/1.50      | sK4 != sK4 ),
% 7.29/1.50      inference(demodulation,[status(thm)],[c_17582,c_9943,c_12642]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(c_17584,plain,
% 7.29/1.50      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 7.29/1.50      inference(equality_resolution_simp,[status(thm)],[c_17583]) ).
% 7.29/1.50  
% 7.29/1.50  cnf(contradiction,plain,
% 7.29/1.50      ( $false ),
% 7.29/1.50      inference(minisat,[status(thm)],[c_17980,c_17584,c_36,c_34,c_31]) ).
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.29/1.50  
% 7.29/1.50  ------                               Statistics
% 7.29/1.50  
% 7.29/1.50  ------ General
% 7.29/1.50  
% 7.29/1.50  abstr_ref_over_cycles:                  0
% 7.29/1.50  abstr_ref_under_cycles:                 0
% 7.29/1.50  gc_basic_clause_elim:                   0
% 7.29/1.50  forced_gc_time:                         0
% 7.29/1.50  parsing_time:                           0.014
% 7.29/1.50  unif_index_cands_time:                  0.
% 7.29/1.50  unif_index_add_time:                    0.
% 7.29/1.50  orderings_time:                         0.
% 7.29/1.50  out_proof_time:                         0.023
% 7.29/1.50  total_time:                             0.997
% 7.29/1.50  num_of_symbols:                         56
% 7.29/1.50  num_of_terms:                           41109
% 7.29/1.50  
% 7.29/1.50  ------ Preprocessing
% 7.29/1.50  
% 7.29/1.50  num_of_splits:                          0
% 7.29/1.50  num_of_split_atoms:                     0
% 7.29/1.50  num_of_reused_defs:                     0
% 7.29/1.50  num_eq_ax_congr_red:                    9
% 7.29/1.50  num_of_sem_filtered_clauses:            1
% 7.29/1.50  num_of_subtypes:                        2
% 7.29/1.50  monotx_restored_types:                  0
% 7.29/1.50  sat_num_of_epr_types:                   0
% 7.29/1.50  sat_num_of_non_cyclic_types:            0
% 7.29/1.50  sat_guarded_non_collapsed_types:        1
% 7.29/1.50  num_pure_diseq_elim:                    0
% 7.29/1.50  simp_replaced_by:                       0
% 7.29/1.50  res_preprocessed:                       143
% 7.29/1.50  prep_upred:                             0
% 7.29/1.50  prep_unflattend:                        7
% 7.29/1.50  smt_new_axioms:                         0
% 7.29/1.50  pred_elim_cands:                        5
% 7.29/1.50  pred_elim:                              3
% 7.29/1.50  pred_elim_cl:                           4
% 7.29/1.50  pred_elim_cycles:                       6
% 7.29/1.50  merged_defs:                            2
% 7.29/1.50  merged_defs_ncl:                        0
% 7.29/1.50  bin_hyper_res:                          2
% 7.29/1.50  prep_cycles:                            4
% 7.29/1.50  pred_elim_time:                         0.004
% 7.29/1.50  splitting_time:                         0.
% 7.29/1.50  sem_filter_time:                        0.
% 7.29/1.50  monotx_time:                            0.
% 7.29/1.50  subtype_inf_time:                       0.001
% 7.29/1.50  
% 7.29/1.50  ------ Problem properties
% 7.29/1.50  
% 7.29/1.50  clauses:                                27
% 7.29/1.50  conjectures:                            13
% 7.29/1.50  epr:                                    8
% 7.29/1.50  horn:                                   21
% 7.29/1.50  ground:                                 14
% 7.29/1.50  unary:                                  14
% 7.29/1.50  binary:                                 4
% 7.29/1.50  lits:                                   115
% 7.29/1.50  lits_eq:                                17
% 7.29/1.50  fd_pure:                                0
% 7.29/1.50  fd_pseudo:                              0
% 7.29/1.50  fd_cond:                                0
% 7.29/1.50  fd_pseudo_cond:                         0
% 7.29/1.50  ac_symbols:                             0
% 7.29/1.50  
% 7.29/1.50  ------ Propositional Solver
% 7.29/1.50  
% 7.29/1.50  prop_solver_calls:                      29
% 7.29/1.50  prop_fast_solver_calls:                 2983
% 7.29/1.50  smt_solver_calls:                       0
% 7.29/1.50  smt_fast_solver_calls:                  0
% 7.29/1.50  prop_num_of_clauses:                    7638
% 7.29/1.50  prop_preprocess_simplified:             15449
% 7.29/1.50  prop_fo_subsumed:                       229
% 7.29/1.50  prop_solver_time:                       0.
% 7.29/1.50  smt_solver_time:                        0.
% 7.29/1.50  smt_fast_solver_time:                   0.
% 7.29/1.50  prop_fast_solver_time:                  0.
% 7.29/1.50  prop_unsat_core_time:                   0.001
% 7.29/1.50  
% 7.29/1.50  ------ QBF
% 7.29/1.50  
% 7.29/1.50  qbf_q_res:                              0
% 7.29/1.50  qbf_num_tautologies:                    0
% 7.29/1.50  qbf_prep_cycles:                        0
% 7.29/1.50  
% 7.29/1.50  ------ BMC1
% 7.29/1.50  
% 7.29/1.50  bmc1_current_bound:                     -1
% 7.29/1.50  bmc1_last_solved_bound:                 -1
% 7.29/1.50  bmc1_unsat_core_size:                   -1
% 7.29/1.50  bmc1_unsat_core_parents_size:           -1
% 7.29/1.50  bmc1_merge_next_fun:                    0
% 7.29/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.29/1.50  
% 7.29/1.50  ------ Instantiation
% 7.29/1.50  
% 7.29/1.50  inst_num_of_clauses:                    1773
% 7.29/1.50  inst_num_in_passive:                    914
% 7.29/1.50  inst_num_in_active:                     682
% 7.29/1.50  inst_num_in_unprocessed:                177
% 7.29/1.50  inst_num_of_loops:                      730
% 7.29/1.50  inst_num_of_learning_restarts:          0
% 7.29/1.50  inst_num_moves_active_passive:          45
% 7.29/1.50  inst_lit_activity:                      0
% 7.29/1.50  inst_lit_activity_moves:                1
% 7.29/1.50  inst_num_tautologies:                   0
% 7.29/1.50  inst_num_prop_implied:                  0
% 7.29/1.50  inst_num_existing_simplified:           0
% 7.29/1.50  inst_num_eq_res_simplified:             0
% 7.29/1.50  inst_num_child_elim:                    0
% 7.29/1.50  inst_num_of_dismatching_blockings:      55
% 7.29/1.50  inst_num_of_non_proper_insts:           1082
% 7.29/1.50  inst_num_of_duplicates:                 0
% 7.29/1.50  inst_inst_num_from_inst_to_res:         0
% 7.29/1.50  inst_dismatching_checking_time:         0.
% 7.29/1.50  
% 7.29/1.50  ------ Resolution
% 7.29/1.50  
% 7.29/1.50  res_num_of_clauses:                     0
% 7.29/1.50  res_num_in_passive:                     0
% 7.29/1.50  res_num_in_active:                      0
% 7.29/1.50  res_num_of_loops:                       147
% 7.29/1.50  res_forward_subset_subsumed:            43
% 7.29/1.50  res_backward_subset_subsumed:           0
% 7.29/1.50  res_forward_subsumed:                   0
% 7.29/1.50  res_backward_subsumed:                  0
% 7.29/1.50  res_forward_subsumption_resolution:     0
% 7.29/1.50  res_backward_subsumption_resolution:    0
% 7.29/1.50  res_clause_to_clause_subsumption:       2429
% 7.29/1.50  res_orphan_elimination:                 0
% 7.29/1.50  res_tautology_del:                      27
% 7.29/1.50  res_num_eq_res_simplified:              0
% 7.29/1.50  res_num_sel_changes:                    0
% 7.29/1.50  res_moves_from_active_to_pass:          0
% 7.29/1.50  
% 7.29/1.50  ------ Superposition
% 7.29/1.50  
% 7.29/1.50  sup_time_total:                         0.
% 7.29/1.50  sup_time_generating:                    0.
% 7.29/1.50  sup_time_sim_full:                      0.
% 7.29/1.50  sup_time_sim_immed:                     0.
% 7.29/1.50  
% 7.29/1.50  sup_num_of_clauses:                     247
% 7.29/1.50  sup_num_in_active:                      143
% 7.29/1.50  sup_num_in_passive:                     104
% 7.29/1.50  sup_num_of_loops:                       145
% 7.29/1.50  sup_fw_superposition:                   204
% 7.29/1.50  sup_bw_superposition:                   65
% 7.29/1.50  sup_immediate_simplified:               111
% 7.29/1.50  sup_given_eliminated:                   0
% 7.29/1.50  comparisons_done:                       0
% 7.29/1.50  comparisons_avoided:                    0
% 7.29/1.50  
% 7.29/1.50  ------ Simplifications
% 7.29/1.50  
% 7.29/1.50  
% 7.29/1.50  sim_fw_subset_subsumed:                 0
% 7.29/1.50  sim_bw_subset_subsumed:                 1
% 7.29/1.50  sim_fw_subsumed:                        12
% 7.29/1.50  sim_bw_subsumed:                        8
% 7.29/1.50  sim_fw_subsumption_res:                 1
% 7.29/1.50  sim_bw_subsumption_res:                 0
% 7.29/1.50  sim_tautology_del:                      0
% 7.29/1.50  sim_eq_tautology_del:                   6
% 7.29/1.50  sim_eq_res_simp:                        6
% 7.29/1.50  sim_fw_demodulated:                     63
% 7.29/1.50  sim_bw_demodulated:                     3
% 7.29/1.50  sim_light_normalised:                   44
% 7.29/1.50  sim_joinable_taut:                      0
% 7.29/1.50  sim_joinable_simp:                      0
% 7.29/1.50  sim_ac_normalised:                      0
% 7.29/1.50  sim_smt_subsumption:                    0
% 7.29/1.50  
%------------------------------------------------------------------------------
