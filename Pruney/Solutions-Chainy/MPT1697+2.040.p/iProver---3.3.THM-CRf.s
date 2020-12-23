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
% DateTime   : Thu Dec  3 12:21:30 EST 2020

% Result     : Theorem 6.79s
% Output     : CNFRefutation 6.79s
% Verified   : 
% Statistics : Number of formulae       :  203 (2130 expanded)
%              Number of clauses        :  137 ( 561 expanded)
%              Number of leaves         :   17 ( 831 expanded)
%              Depth                    :   26
%              Number of atoms          : 1246 (27847 expanded)
%              Number of equality atoms :  550 (6759 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f37,plain,(
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

fof(f36,plain,(
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

fof(f35,plain,(
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

fof(f34,plain,(
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

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f38,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f26,f37,f36,f35,f34,f33,f32])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
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
    inference(equality_resolution,[],[f51])).

fof(f10,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f58,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
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
    inference(equality_resolution,[],[f50])).

fof(f69,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_849,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1337,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_849])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_855,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | ~ v1_funct_1(X0_51)
    | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1332,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X2_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_855])).

cnf(c_2613,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1332])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1726,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_1897,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(instantiation,[status(thm)],[c_1726])).

cnf(c_2811,plain,
    ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2613,c_20,c_18,c_1897])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_843,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1343,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_843])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_858,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1329,plain,
    ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
    | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_858])).

cnf(c_2534,plain,
    ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
    inference(superposition,[status(thm)],[c_1343,c_1329])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_846,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1340,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_846])).

cnf(c_2614,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_1332])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1731,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
    inference(instantiation,[status(thm)],[c_855])).

cnf(c_1902,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_2816,plain,
    ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2614,c_23,c_21,c_1902])).

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
    inference(cnf_transformation,[],[f72])).

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
    inference(cnf_transformation,[],[f53])).

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
    inference(cnf_transformation,[],[f54])).

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
    inference(cnf_transformation,[],[f55])).

cnf(c_175,plain,
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

cnf(c_176,plain,
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
    inference(renaming,[status(thm)],[c_175])).

cnf(c_836,plain,
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
    inference(subtyping,[status(esa)],[c_176])).

cnf(c_1350,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_857,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_xboole_0(X1_51)
    | v1_xboole_0(X0_51) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1330,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_xboole_0(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_857])).

cnf(c_1551,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X0_51,X4_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X0_51,X4_51))
    | k2_partfun1(k4_subset_1(X3_51,X0_51,X4_51),X1_51,k1_tmap_1(X3_51,X1_51,X0_51,X4_51,X2_51,X5_51),X4_51) = X5_51
    | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1350,c_1330])).

cnf(c_5243,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
    | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2816,c_1551])).

cnf(c_29,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_32,plain,
    ( v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_33,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_38,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_39,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_40,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13720,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),X0_51) = X1_51
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5243,c_32,c_33,c_38,c_39,c_40])).

cnf(c_13721,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
    | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),X0_51) = X1_51
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_13720])).

cnf(c_13742,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51
    | k2_partfun1(sK3,sK1,X0_51,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_13721])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_227,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_436,plain,
    ( r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_437,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_26,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_439,plain,
    ( r1_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_28,c_26])).

cnf(c_487,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_227,c_439])).

cnf(c_488,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_487])).

cnf(c_832,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_488])).

cnf(c_13839,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_51,k1_xboole_0)
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13742,c_832])).

cnf(c_13840,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51
    | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13839,c_2534])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_856,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1331,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_856])).

cnf(c_2128,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_1331])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_492,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0
    | k1_relat_1(X0) != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_493,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_831,plain,
    ( ~ v1_relat_1(X0_51)
    | k7_relat_1(X0_51,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_493])).

cnf(c_1353,plain,
    ( k7_relat_1(X0_51,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_831])).

cnf(c_2482,plain,
    ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2128,c_1353])).

cnf(c_13841,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51
    | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13840,c_832,c_2482])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_35,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_14061,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13841,c_34,c_35,c_36])).

cnf(c_14062,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51
    | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_14061])).

cnf(c_14072,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2811,c_14062])).

cnf(c_2127,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_1331])).

cnf(c_2479,plain,
    ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2127,c_1353])).

cnf(c_14073,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14072,c_2479])).

cnf(c_14074,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_14073])).

cnf(c_853,plain,
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

cnf(c_1334,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_853])).

cnf(c_1496,plain,
    ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
    | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
    | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1334,c_1330])).

cnf(c_3125,plain,
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
    | v1_xboole_0(X3_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_1332])).

cnf(c_851,plain,
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

cnf(c_1336,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_1444,plain,
    ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
    | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
    | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(X3_51) != iProver_top
    | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51)) = iProver_top
    | v1_xboole_0(X2_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1336,c_1330])).

cnf(c_8040,plain,
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
    | v1_xboole_0(X3_51) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3125,c_1444])).

cnf(c_8044,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1337,c_8040])).

cnf(c_41,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_42,plain,
    ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8143,plain,
    ( v1_funct_1(X2_51) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8044,c_32,c_35,c_41,c_42])).

cnf(c_8144,plain,
    ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
    | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X1_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_8143])).

cnf(c_8157,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_8144])).

cnf(c_9189,plain,
    ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
    | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8157,c_33,c_38,c_39])).

cnf(c_9198,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51)
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1343,c_9189])).

cnf(c_9203,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9198,c_34])).

cnf(c_14075,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_14074,c_9203])).

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
    inference(cnf_transformation,[],[f73])).

cnf(c_168,plain,
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

cnf(c_169,plain,
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
    inference(renaming,[status(thm)],[c_168])).

cnf(c_837,plain,
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
    inference(subtyping,[status(esa)],[c_169])).

cnf(c_1349,plain,
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
    inference(predicate_to_equality,[status(thm)],[c_837])).

cnf(c_1523,plain,
    ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X0_51,X4_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X0_51,X4_51))
    | k2_partfun1(k4_subset_1(X3_51,X0_51,X4_51),X1_51,k1_tmap_1(X3_51,X1_51,X0_51,X4_51,X2_51,X5_51),X0_51) = X2_51
    | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
    | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
    | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
    | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X5_51) != iProver_top
    | v1_funct_1(X2_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(X1_51) = iProver_top
    | v1_xboole_0(X4_51) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1349,c_1330])).

cnf(c_4287,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
    | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),sK2) = sK4
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2816,c_1523])).

cnf(c_11509,plain,
    ( v1_funct_1(X1_51) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),sK2) = sK4
    | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4287,c_32,c_33,c_38,c_39,c_40])).

cnf(c_11510,plain,
    ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
    | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),sK2) = sK4
    | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
    | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
    | v1_funct_1(X1_51) != iProver_top
    | v1_xboole_0(X0_51) = iProver_top ),
    inference(renaming,[status(thm)],[c_11509])).

cnf(c_11531,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_51,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2534,c_11510])).

cnf(c_11628,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_51,k1_xboole_0)
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11531,c_832])).

cnf(c_11629,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11628,c_2534])).

cnf(c_11630,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11629,c_832,c_2482])).

cnf(c_11898,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11630,c_34,c_35,c_36])).

cnf(c_11899,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4
    | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(X0_51,sK3,sK1) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_11898])).

cnf(c_11909,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2811,c_11899])).

cnf(c_11910,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k1_xboole_0 != k1_xboole_0
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11909,c_2479])).

cnf(c_11911,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11910])).

cnf(c_11912,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | v1_funct_2(sK5,sK3,sK1) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11911,c_9203])).

cnf(c_17,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_850,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2666,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_2534,c_850])).

cnf(c_2667,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2666,c_832])).

cnf(c_2908,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2667,c_2479,c_2811,c_2816])).

cnf(c_1663,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_856])).

cnf(c_1828,plain,
    ( ~ v1_relat_1(sK4)
    | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_831])).

cnf(c_2912,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2908,c_21,c_1663,c_1828])).

cnf(c_2913,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(renaming,[status(thm)],[c_2912])).

cnf(c_9207,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
    inference(demodulation,[status(thm)],[c_9203,c_2913])).

cnf(c_9208,plain,
    ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
    inference(demodulation,[status(thm)],[c_9207,c_9203])).

cnf(c_43,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14075,c_11912,c_9208,c_43,c_42,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 13:28:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 6.79/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.79/1.49  
% 6.79/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.79/1.49  
% 6.79/1.49  ------  iProver source info
% 6.79/1.49  
% 6.79/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.79/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.79/1.49  git: non_committed_changes: false
% 6.79/1.49  git: last_make_outside_of_git: false
% 6.79/1.49  
% 6.79/1.49  ------ 
% 6.79/1.49  
% 6.79/1.49  ------ Input Options
% 6.79/1.49  
% 6.79/1.49  --out_options                           all
% 6.79/1.49  --tptp_safe_out                         true
% 6.79/1.49  --problem_path                          ""
% 6.79/1.49  --include_path                          ""
% 6.79/1.49  --clausifier                            res/vclausify_rel
% 6.79/1.49  --clausifier_options                    --mode clausify
% 6.79/1.49  --stdin                                 false
% 6.79/1.49  --stats_out                             all
% 6.79/1.49  
% 6.79/1.49  ------ General Options
% 6.79/1.49  
% 6.79/1.49  --fof                                   false
% 6.79/1.49  --time_out_real                         305.
% 6.79/1.49  --time_out_virtual                      -1.
% 6.79/1.49  --symbol_type_check                     false
% 6.79/1.49  --clausify_out                          false
% 6.79/1.49  --sig_cnt_out                           false
% 6.79/1.49  --trig_cnt_out                          false
% 6.79/1.49  --trig_cnt_out_tolerance                1.
% 6.79/1.49  --trig_cnt_out_sk_spl                   false
% 6.79/1.49  --abstr_cl_out                          false
% 6.79/1.49  
% 6.79/1.49  ------ Global Options
% 6.79/1.49  
% 6.79/1.49  --schedule                              default
% 6.79/1.49  --add_important_lit                     false
% 6.79/1.49  --prop_solver_per_cl                    1000
% 6.79/1.49  --min_unsat_core                        false
% 6.79/1.49  --soft_assumptions                      false
% 6.79/1.49  --soft_lemma_size                       3
% 6.79/1.49  --prop_impl_unit_size                   0
% 6.79/1.49  --prop_impl_unit                        []
% 6.79/1.49  --share_sel_clauses                     true
% 6.79/1.49  --reset_solvers                         false
% 6.79/1.49  --bc_imp_inh                            [conj_cone]
% 6.79/1.49  --conj_cone_tolerance                   3.
% 6.79/1.49  --extra_neg_conj                        none
% 6.79/1.49  --large_theory_mode                     true
% 6.79/1.49  --prolific_symb_bound                   200
% 6.79/1.49  --lt_threshold                          2000
% 6.79/1.49  --clause_weak_htbl                      true
% 6.79/1.49  --gc_record_bc_elim                     false
% 6.79/1.49  
% 6.79/1.49  ------ Preprocessing Options
% 6.79/1.49  
% 6.79/1.49  --preprocessing_flag                    true
% 6.79/1.49  --time_out_prep_mult                    0.1
% 6.79/1.49  --splitting_mode                        input
% 6.79/1.49  --splitting_grd                         true
% 6.79/1.49  --splitting_cvd                         false
% 6.79/1.49  --splitting_cvd_svl                     false
% 6.79/1.49  --splitting_nvd                         32
% 6.79/1.49  --sub_typing                            true
% 6.79/1.49  --prep_gs_sim                           true
% 6.79/1.49  --prep_unflatten                        true
% 6.79/1.49  --prep_res_sim                          true
% 6.79/1.49  --prep_upred                            true
% 6.79/1.49  --prep_sem_filter                       exhaustive
% 6.79/1.49  --prep_sem_filter_out                   false
% 6.79/1.49  --pred_elim                             true
% 6.79/1.49  --res_sim_input                         true
% 6.79/1.49  --eq_ax_congr_red                       true
% 6.79/1.49  --pure_diseq_elim                       true
% 6.79/1.49  --brand_transform                       false
% 6.79/1.49  --non_eq_to_eq                          false
% 6.79/1.49  --prep_def_merge                        true
% 6.79/1.49  --prep_def_merge_prop_impl              false
% 6.79/1.49  --prep_def_merge_mbd                    true
% 6.79/1.49  --prep_def_merge_tr_red                 false
% 6.79/1.49  --prep_def_merge_tr_cl                  false
% 6.79/1.49  --smt_preprocessing                     true
% 6.79/1.49  --smt_ac_axioms                         fast
% 6.79/1.49  --preprocessed_out                      false
% 6.79/1.49  --preprocessed_stats                    false
% 6.79/1.49  
% 6.79/1.49  ------ Abstraction refinement Options
% 6.79/1.49  
% 6.79/1.49  --abstr_ref                             []
% 6.79/1.49  --abstr_ref_prep                        false
% 6.79/1.49  --abstr_ref_until_sat                   false
% 6.79/1.49  --abstr_ref_sig_restrict                funpre
% 6.79/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.79/1.49  --abstr_ref_under                       []
% 6.79/1.49  
% 6.79/1.49  ------ SAT Options
% 6.79/1.49  
% 6.79/1.49  --sat_mode                              false
% 6.79/1.49  --sat_fm_restart_options                ""
% 6.79/1.49  --sat_gr_def                            false
% 6.79/1.49  --sat_epr_types                         true
% 6.79/1.49  --sat_non_cyclic_types                  false
% 6.79/1.49  --sat_finite_models                     false
% 6.79/1.49  --sat_fm_lemmas                         false
% 6.79/1.49  --sat_fm_prep                           false
% 6.79/1.49  --sat_fm_uc_incr                        true
% 6.79/1.49  --sat_out_model                         small
% 6.79/1.49  --sat_out_clauses                       false
% 6.79/1.49  
% 6.79/1.49  ------ QBF Options
% 6.79/1.49  
% 6.79/1.49  --qbf_mode                              false
% 6.79/1.49  --qbf_elim_univ                         false
% 6.79/1.49  --qbf_dom_inst                          none
% 6.79/1.49  --qbf_dom_pre_inst                      false
% 6.79/1.49  --qbf_sk_in                             false
% 6.79/1.49  --qbf_pred_elim                         true
% 6.79/1.49  --qbf_split                             512
% 6.79/1.49  
% 6.79/1.49  ------ BMC1 Options
% 6.79/1.49  
% 6.79/1.49  --bmc1_incremental                      false
% 6.79/1.49  --bmc1_axioms                           reachable_all
% 6.79/1.49  --bmc1_min_bound                        0
% 6.79/1.49  --bmc1_max_bound                        -1
% 6.79/1.49  --bmc1_max_bound_default                -1
% 6.79/1.49  --bmc1_symbol_reachability              true
% 6.79/1.49  --bmc1_property_lemmas                  false
% 6.79/1.49  --bmc1_k_induction                      false
% 6.79/1.49  --bmc1_non_equiv_states                 false
% 6.79/1.49  --bmc1_deadlock                         false
% 6.79/1.49  --bmc1_ucm                              false
% 6.79/1.49  --bmc1_add_unsat_core                   none
% 6.79/1.49  --bmc1_unsat_core_children              false
% 6.79/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.79/1.49  --bmc1_out_stat                         full
% 6.79/1.49  --bmc1_ground_init                      false
% 6.79/1.49  --bmc1_pre_inst_next_state              false
% 6.79/1.49  --bmc1_pre_inst_state                   false
% 6.79/1.49  --bmc1_pre_inst_reach_state             false
% 6.79/1.49  --bmc1_out_unsat_core                   false
% 6.79/1.49  --bmc1_aig_witness_out                  false
% 6.79/1.49  --bmc1_verbose                          false
% 6.79/1.49  --bmc1_dump_clauses_tptp                false
% 6.79/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.79/1.49  --bmc1_dump_file                        -
% 6.79/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.79/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.79/1.49  --bmc1_ucm_extend_mode                  1
% 6.79/1.49  --bmc1_ucm_init_mode                    2
% 6.79/1.49  --bmc1_ucm_cone_mode                    none
% 6.79/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.79/1.49  --bmc1_ucm_relax_model                  4
% 6.79/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.79/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.79/1.49  --bmc1_ucm_layered_model                none
% 6.79/1.49  --bmc1_ucm_max_lemma_size               10
% 6.79/1.49  
% 6.79/1.49  ------ AIG Options
% 6.79/1.49  
% 6.79/1.49  --aig_mode                              false
% 6.79/1.49  
% 6.79/1.49  ------ Instantiation Options
% 6.79/1.49  
% 6.79/1.49  --instantiation_flag                    true
% 6.79/1.49  --inst_sos_flag                         false
% 6.79/1.49  --inst_sos_phase                        true
% 6.79/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.79/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.79/1.49  --inst_lit_sel_side                     num_symb
% 6.79/1.49  --inst_solver_per_active                1400
% 6.79/1.49  --inst_solver_calls_frac                1.
% 6.79/1.49  --inst_passive_queue_type               priority_queues
% 6.79/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.79/1.49  --inst_passive_queues_freq              [25;2]
% 6.79/1.49  --inst_dismatching                      true
% 6.79/1.49  --inst_eager_unprocessed_to_passive     true
% 6.79/1.49  --inst_prop_sim_given                   true
% 6.79/1.49  --inst_prop_sim_new                     false
% 6.79/1.49  --inst_subs_new                         false
% 6.79/1.49  --inst_eq_res_simp                      false
% 6.79/1.49  --inst_subs_given                       false
% 6.79/1.49  --inst_orphan_elimination               true
% 6.79/1.49  --inst_learning_loop_flag               true
% 6.79/1.49  --inst_learning_start                   3000
% 6.79/1.49  --inst_learning_factor                  2
% 6.79/1.49  --inst_start_prop_sim_after_learn       3
% 6.79/1.49  --inst_sel_renew                        solver
% 6.79/1.49  --inst_lit_activity_flag                true
% 6.79/1.49  --inst_restr_to_given                   false
% 6.79/1.49  --inst_activity_threshold               500
% 6.79/1.49  --inst_out_proof                        true
% 6.79/1.49  
% 6.79/1.49  ------ Resolution Options
% 6.79/1.49  
% 6.79/1.49  --resolution_flag                       true
% 6.79/1.49  --res_lit_sel                           adaptive
% 6.79/1.49  --res_lit_sel_side                      none
% 6.79/1.49  --res_ordering                          kbo
% 6.79/1.49  --res_to_prop_solver                    active
% 6.79/1.49  --res_prop_simpl_new                    false
% 6.79/1.49  --res_prop_simpl_given                  true
% 6.79/1.49  --res_passive_queue_type                priority_queues
% 6.79/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.79/1.49  --res_passive_queues_freq               [15;5]
% 6.79/1.49  --res_forward_subs                      full
% 6.79/1.49  --res_backward_subs                     full
% 6.79/1.49  --res_forward_subs_resolution           true
% 6.79/1.49  --res_backward_subs_resolution          true
% 6.79/1.49  --res_orphan_elimination                true
% 6.79/1.49  --res_time_limit                        2.
% 6.79/1.49  --res_out_proof                         true
% 6.79/1.49  
% 6.79/1.49  ------ Superposition Options
% 6.79/1.49  
% 6.79/1.49  --superposition_flag                    true
% 6.79/1.49  --sup_passive_queue_type                priority_queues
% 6.79/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.79/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.79/1.49  --demod_completeness_check              fast
% 6.79/1.49  --demod_use_ground                      true
% 6.79/1.49  --sup_to_prop_solver                    passive
% 6.79/1.49  --sup_prop_simpl_new                    true
% 6.79/1.49  --sup_prop_simpl_given                  true
% 6.79/1.49  --sup_fun_splitting                     false
% 6.79/1.49  --sup_smt_interval                      50000
% 6.79/1.49  
% 6.79/1.49  ------ Superposition Simplification Setup
% 6.79/1.49  
% 6.79/1.49  --sup_indices_passive                   []
% 6.79/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.79/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.79/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.79/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.79/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.79/1.49  --sup_full_bw                           [BwDemod]
% 6.79/1.49  --sup_immed_triv                        [TrivRules]
% 6.79/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.79/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.79/1.49  --sup_immed_bw_main                     []
% 6.79/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.79/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.79/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.79/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.79/1.49  
% 6.79/1.49  ------ Combination Options
% 6.79/1.49  
% 6.79/1.49  --comb_res_mult                         3
% 6.79/1.49  --comb_sup_mult                         2
% 6.79/1.49  --comb_inst_mult                        10
% 6.79/1.49  
% 6.79/1.49  ------ Debug Options
% 6.79/1.49  
% 6.79/1.49  --dbg_backtrace                         false
% 6.79/1.49  --dbg_dump_prop_clauses                 false
% 6.79/1.49  --dbg_dump_prop_clauses_file            -
% 6.79/1.49  --dbg_out_stat                          false
% 6.79/1.49  ------ Parsing...
% 6.79/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.79/1.49  
% 6.79/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.79/1.49  
% 6.79/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.79/1.49  
% 6.79/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.79/1.49  ------ Proving...
% 6.79/1.49  ------ Problem Properties 
% 6.79/1.49  
% 6.79/1.49  
% 6.79/1.49  clauses                                 29
% 6.79/1.49  conjectures                             13
% 6.79/1.49  EPR                                     8
% 6.79/1.49  Horn                                    23
% 6.79/1.49  unary                                   14
% 6.79/1.49  binary                                  3
% 6.79/1.49  lits                                    122
% 6.79/1.49  lits eq                                 20
% 6.79/1.49  fd_pure                                 0
% 6.79/1.49  fd_pseudo                               0
% 6.79/1.49  fd_cond                                 0
% 6.79/1.49  fd_pseudo_cond                          0
% 6.79/1.49  AC symbols                              0
% 6.79/1.49  
% 6.79/1.49  ------ Schedule dynamic 5 is on 
% 6.79/1.49  
% 6.79/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.79/1.49  
% 6.79/1.49  
% 6.79/1.49  ------ 
% 6.79/1.49  Current options:
% 6.79/1.49  ------ 
% 6.79/1.49  
% 6.79/1.49  ------ Input Options
% 6.79/1.49  
% 6.79/1.49  --out_options                           all
% 6.79/1.49  --tptp_safe_out                         true
% 6.79/1.49  --problem_path                          ""
% 6.79/1.49  --include_path                          ""
% 6.79/1.49  --clausifier                            res/vclausify_rel
% 6.79/1.49  --clausifier_options                    --mode clausify
% 6.79/1.49  --stdin                                 false
% 6.79/1.49  --stats_out                             all
% 6.79/1.49  
% 6.79/1.49  ------ General Options
% 6.79/1.49  
% 6.79/1.49  --fof                                   false
% 6.79/1.49  --time_out_real                         305.
% 6.79/1.49  --time_out_virtual                      -1.
% 6.79/1.49  --symbol_type_check                     false
% 6.79/1.49  --clausify_out                          false
% 6.79/1.49  --sig_cnt_out                           false
% 6.79/1.49  --trig_cnt_out                          false
% 6.79/1.49  --trig_cnt_out_tolerance                1.
% 6.79/1.49  --trig_cnt_out_sk_spl                   false
% 6.79/1.49  --abstr_cl_out                          false
% 6.79/1.49  
% 6.79/1.49  ------ Global Options
% 6.79/1.49  
% 6.79/1.49  --schedule                              default
% 6.79/1.49  --add_important_lit                     false
% 6.79/1.49  --prop_solver_per_cl                    1000
% 6.79/1.49  --min_unsat_core                        false
% 6.79/1.49  --soft_assumptions                      false
% 6.79/1.49  --soft_lemma_size                       3
% 6.79/1.49  --prop_impl_unit_size                   0
% 6.79/1.49  --prop_impl_unit                        []
% 6.79/1.49  --share_sel_clauses                     true
% 6.79/1.49  --reset_solvers                         false
% 6.79/1.49  --bc_imp_inh                            [conj_cone]
% 6.79/1.49  --conj_cone_tolerance                   3.
% 6.79/1.49  --extra_neg_conj                        none
% 6.79/1.49  --large_theory_mode                     true
% 6.79/1.49  --prolific_symb_bound                   200
% 6.79/1.49  --lt_threshold                          2000
% 6.79/1.49  --clause_weak_htbl                      true
% 6.79/1.49  --gc_record_bc_elim                     false
% 6.79/1.49  
% 6.79/1.49  ------ Preprocessing Options
% 6.79/1.49  
% 6.79/1.49  --preprocessing_flag                    true
% 6.79/1.49  --time_out_prep_mult                    0.1
% 6.79/1.49  --splitting_mode                        input
% 6.79/1.49  --splitting_grd                         true
% 6.79/1.49  --splitting_cvd                         false
% 6.79/1.49  --splitting_cvd_svl                     false
% 6.79/1.49  --splitting_nvd                         32
% 6.79/1.49  --sub_typing                            true
% 6.79/1.49  --prep_gs_sim                           true
% 6.79/1.49  --prep_unflatten                        true
% 6.79/1.49  --prep_res_sim                          true
% 6.79/1.49  --prep_upred                            true
% 6.79/1.49  --prep_sem_filter                       exhaustive
% 6.79/1.49  --prep_sem_filter_out                   false
% 6.79/1.49  --pred_elim                             true
% 6.79/1.49  --res_sim_input                         true
% 6.79/1.49  --eq_ax_congr_red                       true
% 6.79/1.49  --pure_diseq_elim                       true
% 6.79/1.49  --brand_transform                       false
% 6.79/1.49  --non_eq_to_eq                          false
% 6.79/1.49  --prep_def_merge                        true
% 6.79/1.49  --prep_def_merge_prop_impl              false
% 6.79/1.49  --prep_def_merge_mbd                    true
% 6.79/1.49  --prep_def_merge_tr_red                 false
% 6.79/1.49  --prep_def_merge_tr_cl                  false
% 6.79/1.49  --smt_preprocessing                     true
% 6.79/1.49  --smt_ac_axioms                         fast
% 6.79/1.49  --preprocessed_out                      false
% 6.79/1.49  --preprocessed_stats                    false
% 6.79/1.49  
% 6.79/1.49  ------ Abstraction refinement Options
% 6.79/1.49  
% 6.79/1.49  --abstr_ref                             []
% 6.79/1.49  --abstr_ref_prep                        false
% 6.79/1.49  --abstr_ref_until_sat                   false
% 6.79/1.49  --abstr_ref_sig_restrict                funpre
% 6.79/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.79/1.49  --abstr_ref_under                       []
% 6.79/1.49  
% 6.79/1.49  ------ SAT Options
% 6.79/1.49  
% 6.79/1.49  --sat_mode                              false
% 6.79/1.49  --sat_fm_restart_options                ""
% 6.79/1.49  --sat_gr_def                            false
% 6.79/1.49  --sat_epr_types                         true
% 6.79/1.49  --sat_non_cyclic_types                  false
% 6.79/1.49  --sat_finite_models                     false
% 6.79/1.49  --sat_fm_lemmas                         false
% 6.79/1.49  --sat_fm_prep                           false
% 6.79/1.49  --sat_fm_uc_incr                        true
% 6.79/1.49  --sat_out_model                         small
% 6.79/1.49  --sat_out_clauses                       false
% 6.79/1.49  
% 6.79/1.49  ------ QBF Options
% 6.79/1.49  
% 6.79/1.49  --qbf_mode                              false
% 6.79/1.49  --qbf_elim_univ                         false
% 6.79/1.49  --qbf_dom_inst                          none
% 6.79/1.49  --qbf_dom_pre_inst                      false
% 6.79/1.49  --qbf_sk_in                             false
% 6.79/1.49  --qbf_pred_elim                         true
% 6.79/1.49  --qbf_split                             512
% 6.79/1.49  
% 6.79/1.49  ------ BMC1 Options
% 6.79/1.49  
% 6.79/1.49  --bmc1_incremental                      false
% 6.79/1.49  --bmc1_axioms                           reachable_all
% 6.79/1.49  --bmc1_min_bound                        0
% 6.79/1.49  --bmc1_max_bound                        -1
% 6.79/1.49  --bmc1_max_bound_default                -1
% 6.79/1.49  --bmc1_symbol_reachability              true
% 6.79/1.49  --bmc1_property_lemmas                  false
% 6.79/1.49  --bmc1_k_induction                      false
% 6.79/1.49  --bmc1_non_equiv_states                 false
% 6.79/1.49  --bmc1_deadlock                         false
% 6.79/1.49  --bmc1_ucm                              false
% 6.79/1.49  --bmc1_add_unsat_core                   none
% 6.79/1.49  --bmc1_unsat_core_children              false
% 6.79/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.79/1.49  --bmc1_out_stat                         full
% 6.79/1.49  --bmc1_ground_init                      false
% 6.79/1.49  --bmc1_pre_inst_next_state              false
% 6.79/1.49  --bmc1_pre_inst_state                   false
% 6.79/1.49  --bmc1_pre_inst_reach_state             false
% 6.79/1.49  --bmc1_out_unsat_core                   false
% 6.79/1.49  --bmc1_aig_witness_out                  false
% 6.79/1.49  --bmc1_verbose                          false
% 6.79/1.49  --bmc1_dump_clauses_tptp                false
% 6.79/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.79/1.49  --bmc1_dump_file                        -
% 6.79/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.79/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.79/1.49  --bmc1_ucm_extend_mode                  1
% 6.79/1.49  --bmc1_ucm_init_mode                    2
% 6.79/1.49  --bmc1_ucm_cone_mode                    none
% 6.79/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.79/1.49  --bmc1_ucm_relax_model                  4
% 6.79/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.79/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.79/1.49  --bmc1_ucm_layered_model                none
% 6.79/1.49  --bmc1_ucm_max_lemma_size               10
% 6.79/1.49  
% 6.79/1.49  ------ AIG Options
% 6.79/1.49  
% 6.79/1.49  --aig_mode                              false
% 6.79/1.49  
% 6.79/1.49  ------ Instantiation Options
% 6.79/1.49  
% 6.79/1.49  --instantiation_flag                    true
% 6.79/1.49  --inst_sos_flag                         false
% 6.79/1.49  --inst_sos_phase                        true
% 6.79/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.79/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.79/1.49  --inst_lit_sel_side                     none
% 6.79/1.49  --inst_solver_per_active                1400
% 6.79/1.49  --inst_solver_calls_frac                1.
% 6.79/1.49  --inst_passive_queue_type               priority_queues
% 6.79/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.79/1.49  --inst_passive_queues_freq              [25;2]
% 6.79/1.49  --inst_dismatching                      true
% 6.79/1.49  --inst_eager_unprocessed_to_passive     true
% 6.79/1.49  --inst_prop_sim_given                   true
% 6.79/1.49  --inst_prop_sim_new                     false
% 6.79/1.49  --inst_subs_new                         false
% 6.79/1.49  --inst_eq_res_simp                      false
% 6.79/1.49  --inst_subs_given                       false
% 6.79/1.49  --inst_orphan_elimination               true
% 6.79/1.49  --inst_learning_loop_flag               true
% 6.79/1.49  --inst_learning_start                   3000
% 6.79/1.49  --inst_learning_factor                  2
% 6.79/1.49  --inst_start_prop_sim_after_learn       3
% 6.79/1.49  --inst_sel_renew                        solver
% 6.79/1.49  --inst_lit_activity_flag                true
% 6.79/1.49  --inst_restr_to_given                   false
% 6.79/1.49  --inst_activity_threshold               500
% 6.79/1.49  --inst_out_proof                        true
% 6.79/1.49  
% 6.79/1.49  ------ Resolution Options
% 6.79/1.49  
% 6.79/1.49  --resolution_flag                       false
% 6.79/1.49  --res_lit_sel                           adaptive
% 6.79/1.49  --res_lit_sel_side                      none
% 6.79/1.49  --res_ordering                          kbo
% 6.79/1.49  --res_to_prop_solver                    active
% 6.79/1.49  --res_prop_simpl_new                    false
% 6.79/1.49  --res_prop_simpl_given                  true
% 6.79/1.49  --res_passive_queue_type                priority_queues
% 6.79/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.79/1.49  --res_passive_queues_freq               [15;5]
% 6.79/1.49  --res_forward_subs                      full
% 6.79/1.49  --res_backward_subs                     full
% 6.79/1.49  --res_forward_subs_resolution           true
% 6.79/1.49  --res_backward_subs_resolution          true
% 6.79/1.49  --res_orphan_elimination                true
% 6.79/1.49  --res_time_limit                        2.
% 6.79/1.49  --res_out_proof                         true
% 6.79/1.49  
% 6.79/1.49  ------ Superposition Options
% 6.79/1.49  
% 6.79/1.49  --superposition_flag                    true
% 6.79/1.49  --sup_passive_queue_type                priority_queues
% 6.79/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.79/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.79/1.49  --demod_completeness_check              fast
% 6.79/1.49  --demod_use_ground                      true
% 6.79/1.49  --sup_to_prop_solver                    passive
% 6.79/1.49  --sup_prop_simpl_new                    true
% 6.79/1.49  --sup_prop_simpl_given                  true
% 6.79/1.49  --sup_fun_splitting                     false
% 6.79/1.49  --sup_smt_interval                      50000
% 6.79/1.49  
% 6.79/1.49  ------ Superposition Simplification Setup
% 6.79/1.49  
% 6.79/1.49  --sup_indices_passive                   []
% 6.79/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.79/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.79/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.79/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.79/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.79/1.49  --sup_full_bw                           [BwDemod]
% 6.79/1.49  --sup_immed_triv                        [TrivRules]
% 6.79/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.79/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.79/1.49  --sup_immed_bw_main                     []
% 6.79/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.79/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.79/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.79/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.79/1.49  
% 6.79/1.49  ------ Combination Options
% 6.79/1.49  
% 6.79/1.49  --comb_res_mult                         3
% 6.79/1.49  --comb_sup_mult                         2
% 6.79/1.49  --comb_inst_mult                        10
% 6.79/1.49  
% 6.79/1.49  ------ Debug Options
% 6.79/1.49  
% 6.79/1.49  --dbg_backtrace                         false
% 6.79/1.49  --dbg_dump_prop_clauses                 false
% 6.79/1.49  --dbg_dump_prop_clauses_file            -
% 6.79/1.49  --dbg_out_stat                          false
% 6.79/1.49  
% 6.79/1.49  
% 6.79/1.49  
% 6.79/1.49  
% 6.79/1.49  ------ Proving...
% 6.79/1.49  
% 6.79/1.49  
% 6.79/1.49  % SZS status Theorem for theBenchmark.p
% 6.79/1.49  
% 6.79/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.79/1.49  
% 6.79/1.49  fof(f11,conjecture,(
% 6.79/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f12,negated_conjecture,(
% 6.79/1.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 6.79/1.49    inference(negated_conjecture,[],[f11])).
% 6.79/1.49  
% 6.79/1.49  fof(f25,plain,(
% 6.79/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.79/1.49    inference(ennf_transformation,[],[f12])).
% 6.79/1.49  
% 6.79/1.49  fof(f26,plain,(
% 6.79/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 6.79/1.49    inference(flattening,[],[f25])).
% 6.79/1.49  
% 6.79/1.49  fof(f37,plain,(
% 6.79/1.49    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 6.79/1.49    introduced(choice_axiom,[])).
% 6.79/1.49  
% 6.79/1.49  fof(f36,plain,(
% 6.79/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 6.79/1.49    introduced(choice_axiom,[])).
% 6.79/1.49  
% 6.79/1.49  fof(f35,plain,(
% 6.79/1.49    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 6.79/1.49    introduced(choice_axiom,[])).
% 6.79/1.49  
% 6.79/1.49  fof(f34,plain,(
% 6.79/1.49    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 6.79/1.49    introduced(choice_axiom,[])).
% 6.79/1.49  
% 6.79/1.49  fof(f33,plain,(
% 6.79/1.49    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 6.79/1.49    introduced(choice_axiom,[])).
% 6.79/1.49  
% 6.79/1.49  fof(f32,plain,(
% 6.79/1.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 6.79/1.49    introduced(choice_axiom,[])).
% 6.79/1.49  
% 6.79/1.49  fof(f38,plain,(
% 6.79/1.49    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 6.79/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f26,f37,f36,f35,f34,f33,f32])).
% 6.79/1.49  
% 6.79/1.49  fof(f68,plain,(
% 6.79/1.49    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f8,axiom,(
% 6.79/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f19,plain,(
% 6.79/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.79/1.49    inference(ennf_transformation,[],[f8])).
% 6.79/1.49  
% 6.79/1.49  fof(f20,plain,(
% 6.79/1.49    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.79/1.49    inference(flattening,[],[f19])).
% 6.79/1.49  
% 6.79/1.49  fof(f49,plain,(
% 6.79/1.49    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f20])).
% 6.79/1.49  
% 6.79/1.49  fof(f66,plain,(
% 6.79/1.49    v1_funct_1(sK5)),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f61,plain,(
% 6.79/1.49    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f3,axiom,(
% 6.79/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f13,plain,(
% 6.79/1.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.79/1.49    inference(ennf_transformation,[],[f3])).
% 6.79/1.49  
% 6.79/1.49  fof(f42,plain,(
% 6.79/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.79/1.49    inference(cnf_transformation,[],[f13])).
% 6.79/1.49  
% 6.79/1.49  fof(f65,plain,(
% 6.79/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f63,plain,(
% 6.79/1.49    v1_funct_1(sK4)),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f9,axiom,(
% 6.79/1.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f21,plain,(
% 6.79/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.79/1.49    inference(ennf_transformation,[],[f9])).
% 6.79/1.49  
% 6.79/1.49  fof(f22,plain,(
% 6.79/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.79/1.49    inference(flattening,[],[f21])).
% 6.79/1.49  
% 6.79/1.49  fof(f30,plain,(
% 6.79/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.79/1.49    inference(nnf_transformation,[],[f22])).
% 6.79/1.49  
% 6.79/1.49  fof(f31,plain,(
% 6.79/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 6.79/1.49    inference(flattening,[],[f30])).
% 6.79/1.49  
% 6.79/1.49  fof(f51,plain,(
% 6.79/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f31])).
% 6.79/1.49  
% 6.79/1.49  fof(f72,plain,(
% 6.79/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.79/1.49    inference(equality_resolution,[],[f51])).
% 6.79/1.49  
% 6.79/1.49  fof(f10,axiom,(
% 6.79/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f23,plain,(
% 6.79/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.79/1.49    inference(ennf_transformation,[],[f10])).
% 6.79/1.49  
% 6.79/1.49  fof(f24,plain,(
% 6.79/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.79/1.49    inference(flattening,[],[f23])).
% 6.79/1.49  
% 6.79/1.49  fof(f53,plain,(
% 6.79/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f24])).
% 6.79/1.49  
% 6.79/1.49  fof(f54,plain,(
% 6.79/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f24])).
% 6.79/1.49  
% 6.79/1.49  fof(f55,plain,(
% 6.79/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f24])).
% 6.79/1.49  
% 6.79/1.49  fof(f4,axiom,(
% 6.79/1.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f14,plain,(
% 6.79/1.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 6.79/1.49    inference(ennf_transformation,[],[f4])).
% 6.79/1.49  
% 6.79/1.49  fof(f43,plain,(
% 6.79/1.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f14])).
% 6.79/1.49  
% 6.79/1.49  fof(f57,plain,(
% 6.79/1.49    ~v1_xboole_0(sK1)),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f58,plain,(
% 6.79/1.49    ~v1_xboole_0(sK2)),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f64,plain,(
% 6.79/1.49    v1_funct_2(sK4,sK2,sK1)),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f1,axiom,(
% 6.79/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f27,plain,(
% 6.79/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.79/1.49    inference(nnf_transformation,[],[f1])).
% 6.79/1.49  
% 6.79/1.49  fof(f39,plain,(
% 6.79/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f27])).
% 6.79/1.49  
% 6.79/1.49  fof(f6,axiom,(
% 6.79/1.49    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f16,plain,(
% 6.79/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 6.79/1.49    inference(ennf_transformation,[],[f6])).
% 6.79/1.49  
% 6.79/1.49  fof(f17,plain,(
% 6.79/1.49    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.79/1.49    inference(flattening,[],[f16])).
% 6.79/1.49  
% 6.79/1.49  fof(f29,plain,(
% 6.79/1.49    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 6.79/1.49    inference(nnf_transformation,[],[f17])).
% 6.79/1.49  
% 6.79/1.49  fof(f46,plain,(
% 6.79/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f29])).
% 6.79/1.49  
% 6.79/1.49  fof(f62,plain,(
% 6.79/1.49    r1_subset_1(sK2,sK3)),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f60,plain,(
% 6.79/1.49    ~v1_xboole_0(sK3)),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f7,axiom,(
% 6.79/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f18,plain,(
% 6.79/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.79/1.49    inference(ennf_transformation,[],[f7])).
% 6.79/1.49  
% 6.79/1.49  fof(f48,plain,(
% 6.79/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.79/1.49    inference(cnf_transformation,[],[f18])).
% 6.79/1.49  
% 6.79/1.49  fof(f2,axiom,(
% 6.79/1.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f41,plain,(
% 6.79/1.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f2])).
% 6.79/1.49  
% 6.79/1.49  fof(f5,axiom,(
% 6.79/1.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 6.79/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.79/1.49  
% 6.79/1.49  fof(f15,plain,(
% 6.79/1.49    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.79/1.49    inference(ennf_transformation,[],[f5])).
% 6.79/1.49  
% 6.79/1.49  fof(f28,plain,(
% 6.79/1.49    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.79/1.49    inference(nnf_transformation,[],[f15])).
% 6.79/1.49  
% 6.79/1.49  fof(f45,plain,(
% 6.79/1.49    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f28])).
% 6.79/1.49  
% 6.79/1.49  fof(f59,plain,(
% 6.79/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f67,plain,(
% 6.79/1.49    v1_funct_2(sK5,sK3,sK1)),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  fof(f50,plain,(
% 6.79/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.79/1.49    inference(cnf_transformation,[],[f31])).
% 6.79/1.49  
% 6.79/1.49  fof(f73,plain,(
% 6.79/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 6.79/1.49    inference(equality_resolution,[],[f50])).
% 6.79/1.49  
% 6.79/1.49  fof(f69,plain,(
% 6.79/1.49    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 6.79/1.49    inference(cnf_transformation,[],[f38])).
% 6.79/1.49  
% 6.79/1.49  cnf(c_18,negated_conjecture,
% 6.79/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 6.79/1.49      inference(cnf_transformation,[],[f68]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_849,negated_conjecture,
% 6.79/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_18]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1337,plain,
% 6.79/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_849]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_10,plain,
% 6.79/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | ~ v1_funct_1(X0)
% 6.79/1.49      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 6.79/1.49      inference(cnf_transformation,[],[f49]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_855,plain,
% 6.79/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.79/1.49      | ~ v1_funct_1(X0_51)
% 6.79/1.49      | k2_partfun1(X1_51,X2_51,X0_51,X3_51) = k7_relat_1(X0_51,X3_51) ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_10]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1332,plain,
% 6.79/1.49      ( k2_partfun1(X0_51,X1_51,X2_51,X3_51) = k7_relat_1(X2_51,X3_51)
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 6.79/1.49      | v1_funct_1(X2_51) != iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_855]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2613,plain,
% 6.79/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51)
% 6.79/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_1337,c_1332]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_20,negated_conjecture,
% 6.79/1.49      ( v1_funct_1(sK5) ),
% 6.79/1.49      inference(cnf_transformation,[],[f66]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1726,plain,
% 6.79/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 6.79/1.49      | ~ v1_funct_1(sK5)
% 6.79/1.49      | k2_partfun1(X0_51,X1_51,sK5,X2_51) = k7_relat_1(sK5,X2_51) ),
% 6.79/1.49      inference(instantiation,[status(thm)],[c_855]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1897,plain,
% 6.79/1.49      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 6.79/1.49      | ~ v1_funct_1(sK5)
% 6.79/1.49      | k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 6.79/1.49      inference(instantiation,[status(thm)],[c_1726]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2811,plain,
% 6.79/1.49      ( k2_partfun1(sK3,sK1,sK5,X0_51) = k7_relat_1(sK5,X0_51) ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_2613,c_20,c_18,c_1897]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_25,negated_conjecture,
% 6.79/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 6.79/1.49      inference(cnf_transformation,[],[f61]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_843,negated_conjecture,
% 6.79/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_25]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1343,plain,
% 6.79/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_843]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_3,plain,
% 6.79/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.79/1.49      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 6.79/1.49      inference(cnf_transformation,[],[f42]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_858,plain,
% 6.79/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 6.79/1.49      | k9_subset_1(X1_51,X2_51,X0_51) = k3_xboole_0(X2_51,X0_51) ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_3]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1329,plain,
% 6.79/1.49      ( k9_subset_1(X0_51,X1_51,X2_51) = k3_xboole_0(X1_51,X2_51)
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_858]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2534,plain,
% 6.79/1.49      ( k9_subset_1(sK0,X0_51,sK3) = k3_xboole_0(X0_51,sK3) ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_1343,c_1329]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_21,negated_conjecture,
% 6.79/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 6.79/1.49      inference(cnf_transformation,[],[f65]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_846,negated_conjecture,
% 6.79/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_21]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1340,plain,
% 6.79/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_846]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2614,plain,
% 6.79/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51)
% 6.79/1.49      | v1_funct_1(sK4) != iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_1340,c_1332]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_23,negated_conjecture,
% 6.79/1.49      ( v1_funct_1(sK4) ),
% 6.79/1.49      inference(cnf_transformation,[],[f63]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1731,plain,
% 6.79/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 6.79/1.49      | ~ v1_funct_1(sK4)
% 6.79/1.49      | k2_partfun1(X0_51,X1_51,sK4,X2_51) = k7_relat_1(sK4,X2_51) ),
% 6.79/1.49      inference(instantiation,[status(thm)],[c_855]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1902,plain,
% 6.79/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.79/1.49      | ~ v1_funct_1(sK4)
% 6.79/1.49      | k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 6.79/1.49      inference(instantiation,[status(thm)],[c_1731]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2816,plain,
% 6.79/1.49      ( k2_partfun1(sK2,sK1,sK4,X0_51) = k7_relat_1(sK4,X0_51) ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_2614,c_23,c_21,c_1902]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_12,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.79/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.79/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.79/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.79/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.79/1.49      | ~ v1_funct_1(X0)
% 6.79/1.49      | ~ v1_funct_1(X3)
% 6.79/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.79/1.49      | v1_xboole_0(X5)
% 6.79/1.49      | v1_xboole_0(X2)
% 6.79/1.49      | v1_xboole_0(X4)
% 6.79/1.49      | v1_xboole_0(X1)
% 6.79/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.79/1.49      inference(cnf_transformation,[],[f72]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_16,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.79/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.79/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.79/1.49      | ~ v1_funct_1(X0)
% 6.79/1.49      | ~ v1_funct_1(X3)
% 6.79/1.49      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.79/1.49      | v1_xboole_0(X5)
% 6.79/1.49      | v1_xboole_0(X2)
% 6.79/1.49      | v1_xboole_0(X4)
% 6.79/1.49      | v1_xboole_0(X1) ),
% 6.79/1.49      inference(cnf_transformation,[],[f53]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_15,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.79/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.79/1.49      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.79/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.79/1.49      | ~ v1_funct_1(X0)
% 6.79/1.49      | ~ v1_funct_1(X3)
% 6.79/1.49      | v1_xboole_0(X5)
% 6.79/1.49      | v1_xboole_0(X2)
% 6.79/1.49      | v1_xboole_0(X4)
% 6.79/1.49      | v1_xboole_0(X1) ),
% 6.79/1.49      inference(cnf_transformation,[],[f54]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_14,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.79/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.79/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.79/1.49      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.79/1.49      | ~ v1_funct_1(X0)
% 6.79/1.49      | ~ v1_funct_1(X3)
% 6.79/1.49      | v1_xboole_0(X5)
% 6.79/1.49      | v1_xboole_0(X2)
% 6.79/1.49      | v1_xboole_0(X4)
% 6.79/1.49      | v1_xboole_0(X1) ),
% 6.79/1.49      inference(cnf_transformation,[],[f55]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_175,plain,
% 6.79/1.49      ( ~ v1_funct_1(X3)
% 6.79/1.49      | ~ v1_funct_1(X0)
% 6.79/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.79/1.49      | ~ v1_funct_2(X0,X1,X2)
% 6.79/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.79/1.49      | v1_xboole_0(X5)
% 6.79/1.49      | v1_xboole_0(X2)
% 6.79/1.49      | v1_xboole_0(X4)
% 6.79/1.49      | v1_xboole_0(X1)
% 6.79/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_12,c_16,c_15,c_14]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_176,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.79/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.79/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.79/1.49      | ~ v1_funct_1(X0)
% 6.79/1.49      | ~ v1_funct_1(X3)
% 6.79/1.49      | v1_xboole_0(X1)
% 6.79/1.49      | v1_xboole_0(X2)
% 6.79/1.49      | v1_xboole_0(X4)
% 6.79/1.49      | v1_xboole_0(X5)
% 6.79/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 6.79/1.49      inference(renaming,[status(thm)],[c_175]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_836,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 6.79/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 6.79/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 6.79/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 6.79/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.79/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 6.79/1.49      | ~ v1_funct_1(X0_51)
% 6.79/1.49      | ~ v1_funct_1(X3_51)
% 6.79/1.49      | v1_xboole_0(X1_51)
% 6.79/1.49      | v1_xboole_0(X2_51)
% 6.79/1.49      | v1_xboole_0(X4_51)
% 6.79/1.49      | v1_xboole_0(X5_51)
% 6.79/1.49      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X1_51) = X0_51 ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_176]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1350,plain,
% 6.79/1.49      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X0_51) = X2_51
% 6.79/1.49      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 6.79/1.49      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 6.79/1.49      | v1_funct_1(X2_51) != iProver_top
% 6.79/1.49      | v1_funct_1(X5_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X3_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X4_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_4,plain,
% 6.79/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.79/1.49      | ~ v1_xboole_0(X1)
% 6.79/1.49      | v1_xboole_0(X0) ),
% 6.79/1.49      inference(cnf_transformation,[],[f43]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_857,plain,
% 6.79/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 6.79/1.49      | ~ v1_xboole_0(X1_51)
% 6.79/1.49      | v1_xboole_0(X0_51) ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_4]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1330,plain,
% 6.79/1.49      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_857]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1551,plain,
% 6.79/1.49      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X0_51,X4_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X0_51,X4_51))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X3_51,X0_51,X4_51),X1_51,k1_tmap_1(X3_51,X1_51,X0_51,X4_51,X2_51,X5_51),X4_51) = X5_51
% 6.79/1.49      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 6.79/1.49      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 6.79/1.49      | v1_funct_1(X5_51) != iProver_top
% 6.79/1.49      | v1_funct_1(X2_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X4_51) = iProver_top ),
% 6.79/1.49      inference(forward_subsumption_resolution,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_1350,c_1330]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_5243,plain,
% 6.79/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),X0_51) = X1_51
% 6.79/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.79/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | v1_funct_1(X1_51) != iProver_top
% 6.79/1.49      | v1_funct_1(sK4) != iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(sK1) = iProver_top
% 6.79/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_2816,c_1551]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_29,negated_conjecture,
% 6.79/1.49      ( ~ v1_xboole_0(sK1) ),
% 6.79/1.49      inference(cnf_transformation,[],[f57]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_32,plain,
% 6.79/1.49      ( v1_xboole_0(sK1) != iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_28,negated_conjecture,
% 6.79/1.49      ( ~ v1_xboole_0(sK2) ),
% 6.79/1.49      inference(cnf_transformation,[],[f58]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_33,plain,
% 6.79/1.49      ( v1_xboole_0(sK2) != iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_38,plain,
% 6.79/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_22,negated_conjecture,
% 6.79/1.49      ( v1_funct_2(sK4,sK2,sK1) ),
% 6.79/1.49      inference(cnf_transformation,[],[f64]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_39,plain,
% 6.79/1.49      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_40,plain,
% 6.79/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_13720,plain,
% 6.79/1.49      ( v1_funct_1(X1_51) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.79/1.49      | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),X0_51) = X1_51
% 6.79/1.49      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_5243,c_32,c_33,c_38,c_39,c_40]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_13721,plain,
% 6.79/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),X0_51) = X1_51
% 6.79/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | v1_funct_1(X1_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 6.79/1.49      inference(renaming,[status(thm)],[c_13720]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_13742,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51
% 6.79/1.49      | k2_partfun1(sK3,sK1,X0_51,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_2534,c_13721]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1,plain,
% 6.79/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 6.79/1.49      inference(cnf_transformation,[],[f39]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_227,plain,
% 6.79/1.49      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 6.79/1.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_8,plain,
% 6.79/1.49      ( ~ r1_subset_1(X0,X1)
% 6.79/1.49      | r1_xboole_0(X0,X1)
% 6.79/1.49      | v1_xboole_0(X0)
% 6.79/1.49      | v1_xboole_0(X1) ),
% 6.79/1.49      inference(cnf_transformation,[],[f46]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_24,negated_conjecture,
% 6.79/1.49      ( r1_subset_1(sK2,sK3) ),
% 6.79/1.49      inference(cnf_transformation,[],[f62]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_436,plain,
% 6.79/1.49      ( r1_xboole_0(X0,X1)
% 6.79/1.49      | v1_xboole_0(X0)
% 6.79/1.49      | v1_xboole_0(X1)
% 6.79/1.49      | sK3 != X1
% 6.79/1.49      | sK2 != X0 ),
% 6.79/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_437,plain,
% 6.79/1.49      ( r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) ),
% 6.79/1.49      inference(unflattening,[status(thm)],[c_436]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_26,negated_conjecture,
% 6.79/1.49      ( ~ v1_xboole_0(sK3) ),
% 6.79/1.49      inference(cnf_transformation,[],[f60]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_439,plain,
% 6.79/1.49      ( r1_xboole_0(sK2,sK3) ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_437,c_28,c_26]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_487,plain,
% 6.79/1.49      ( k3_xboole_0(X0,X1) = k1_xboole_0 | sK3 != X1 | sK2 != X0 ),
% 6.79/1.49      inference(resolution_lifted,[status(thm)],[c_227,c_439]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_488,plain,
% 6.79/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 6.79/1.49      inference(unflattening,[status(thm)],[c_487]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_832,plain,
% 6.79/1.49      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_488]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_13839,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51
% 6.79/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_51,k1_xboole_0)
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.79/1.49      inference(light_normalisation,[status(thm)],[c_13742,c_832]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_13840,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51
% 6.79/1.49      | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.79/1.49      inference(demodulation,[status(thm)],[c_13839,c_2534]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_9,plain,
% 6.79/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | v1_relat_1(X0) ),
% 6.79/1.49      inference(cnf_transformation,[],[f48]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_856,plain,
% 6.79/1.49      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.79/1.49      | v1_relat_1(X0_51) ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_9]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1331,plain,
% 6.79/1.49      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 6.79/1.49      | v1_relat_1(X0_51) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_856]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2128,plain,
% 6.79/1.49      ( v1_relat_1(sK4) = iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_1340,c_1331]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2,plain,
% 6.79/1.49      ( r1_xboole_0(X0,k1_xboole_0) ),
% 6.79/1.49      inference(cnf_transformation,[],[f41]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_5,plain,
% 6.79/1.49      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 6.79/1.49      | ~ v1_relat_1(X0)
% 6.79/1.49      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 6.79/1.49      inference(cnf_transformation,[],[f45]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_492,plain,
% 6.79/1.49      ( ~ v1_relat_1(X0)
% 6.79/1.49      | k7_relat_1(X0,X1) = k1_xboole_0
% 6.79/1.49      | k1_relat_1(X0) != X2
% 6.79/1.49      | k1_xboole_0 != X1 ),
% 6.79/1.49      inference(resolution_lifted,[status(thm)],[c_2,c_5]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_493,plain,
% 6.79/1.49      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 6.79/1.49      inference(unflattening,[status(thm)],[c_492]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_831,plain,
% 6.79/1.49      ( ~ v1_relat_1(X0_51)
% 6.79/1.49      | k7_relat_1(X0_51,k1_xboole_0) = k1_xboole_0 ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_493]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1353,plain,
% 6.79/1.49      ( k7_relat_1(X0_51,k1_xboole_0) = k1_xboole_0
% 6.79/1.49      | v1_relat_1(X0_51) != iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_831]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2482,plain,
% 6.79/1.49      ( k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_2128,c_1353]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_13841,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51
% 6.79/1.49      | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.79/1.49      inference(light_normalisation,[status(thm)],[c_13840,c_832,c_2482]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_27,negated_conjecture,
% 6.79/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 6.79/1.49      inference(cnf_transformation,[],[f59]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_34,plain,
% 6.79/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_35,plain,
% 6.79/1.49      ( v1_xboole_0(sK3) != iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_36,plain,
% 6.79/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_14061,plain,
% 6.79/1.49      ( v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
% 6.79/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51 ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_13841,c_34,c_35,c_36]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_14062,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK3) = X0_51
% 6.79/1.49      | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top ),
% 6.79/1.49      inference(renaming,[status(thm)],[c_14061]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_14072,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.79/1.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 6.79/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_2811,c_14062]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2127,plain,
% 6.79/1.49      ( v1_relat_1(sK5) = iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_1337,c_1331]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2479,plain,
% 6.79/1.49      ( k7_relat_1(sK5,k1_xboole_0) = k1_xboole_0 ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_2127,c_1353]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_14073,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.79/1.49      | k1_xboole_0 != k1_xboole_0
% 6.79/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.79/1.49      inference(light_normalisation,[status(thm)],[c_14072,c_2479]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_14074,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.79/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.79/1.49      inference(equality_resolution_simp,[status(thm)],[c_14073]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_853,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 6.79/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 6.79/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 6.79/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 6.79/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.79/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 6.79/1.49      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51)))
% 6.79/1.49      | ~ v1_funct_1(X0_51)
% 6.79/1.49      | ~ v1_funct_1(X3_51)
% 6.79/1.49      | v1_xboole_0(X1_51)
% 6.79/1.49      | v1_xboole_0(X2_51)
% 6.79/1.49      | v1_xboole_0(X4_51)
% 6.79/1.49      | v1_xboole_0(X5_51) ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_14]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1334,plain,
% 6.79/1.49      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 6.79/1.49      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51))) = iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_funct_1(X3_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X5_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X2_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X4_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_853]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1496,plain,
% 6.79/1.49      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 6.79/1.49      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5_51,X4_51,X1_51),X2_51))) = iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_funct_1(X3_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X2_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X4_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top ),
% 6.79/1.49      inference(forward_subsumption_resolution,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_1334,c_1330]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_3125,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
% 6.79/1.49      | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
% 6.79/1.49      | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 6.79/1.49      | v1_funct_1(X5_51) != iProver_top
% 6.79/1.49      | v1_funct_1(X4_51) != iProver_top
% 6.79/1.49      | v1_funct_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51)) != iProver_top
% 6.79/1.49      | v1_xboole_0(X3_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X2_51) = iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_1496,c_1332]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_851,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 6.79/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 6.79/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 6.79/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 6.79/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.79/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 6.79/1.49      | ~ v1_funct_1(X0_51)
% 6.79/1.49      | ~ v1_funct_1(X3_51)
% 6.79/1.49      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51))
% 6.79/1.49      | v1_xboole_0(X1_51)
% 6.79/1.49      | v1_xboole_0(X2_51)
% 6.79/1.49      | v1_xboole_0(X4_51)
% 6.79/1.49      | v1_xboole_0(X5_51) ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_16]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1336,plain,
% 6.79/1.49      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 6.79/1.49      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_funct_1(X3_51) != iProver_top
% 6.79/1.49      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51)) = iProver_top
% 6.79/1.49      | v1_xboole_0(X5_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X2_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X4_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1444,plain,
% 6.79/1.49      ( v1_funct_2(X0_51,X1_51,X2_51) != iProver_top
% 6.79/1.49      | v1_funct_2(X3_51,X4_51,X2_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X5_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51))) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_funct_1(X3_51) != iProver_top
% 6.79/1.49      | v1_funct_1(k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51)) = iProver_top
% 6.79/1.49      | v1_xboole_0(X2_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X4_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top ),
% 6.79/1.49      inference(forward_subsumption_resolution,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_1336,c_1330]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_8040,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,X2_51),X3_51,k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51) = k7_relat_1(k1_tmap_1(X0_51,X3_51,X1_51,X2_51,X4_51,X5_51),X6_51)
% 6.79/1.49      | v1_funct_2(X5_51,X2_51,X3_51) != iProver_top
% 6.79/1.49      | v1_funct_2(X4_51,X1_51,X3_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X2_51,X3_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X3_51))) != iProver_top
% 6.79/1.49      | v1_funct_1(X5_51) != iProver_top
% 6.79/1.49      | v1_funct_1(X4_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X2_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X3_51) = iProver_top ),
% 6.79/1.49      inference(forward_subsumption_resolution,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_3125,c_1444]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_8044,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 6.79/1.49      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 6.79/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | v1_funct_1(X2_51) != iProver_top
% 6.79/1.49      | v1_funct_1(sK5) != iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(sK1) = iProver_top
% 6.79/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_1337,c_8040]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_41,plain,
% 6.79/1.49      ( v1_funct_1(sK5) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_19,negated_conjecture,
% 6.79/1.49      ( v1_funct_2(sK5,sK3,sK1) ),
% 6.79/1.49      inference(cnf_transformation,[],[f67]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_42,plain,
% 6.79/1.49      ( v1_funct_2(sK5,sK3,sK1) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_8143,plain,
% 6.79/1.49      ( v1_funct_1(X2_51) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 6.79/1.49      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_8044,c_32,c_35,c_41,c_42]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_8144,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(X0_51,X1_51,sK3),sK1,k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,X1_51,sK3,X2_51,sK5),X3_51)
% 6.79/1.49      | v1_funct_2(X2_51,X1_51,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | v1_funct_1(X2_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top ),
% 6.79/1.49      inference(renaming,[status(thm)],[c_8143]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_8157,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 6.79/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | v1_funct_1(sK4) != iProver_top
% 6.79/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_1340,c_8144]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_9189,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(X0_51,sK2,sK3),sK1,k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51) = k7_relat_1(k1_tmap_1(X0_51,sK1,sK2,sK3,sK4,sK5),X1_51)
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(X0_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X0_51)) != iProver_top ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_8157,c_33,c_38,c_39]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_9198,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51)
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_1343,c_9189]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_9203,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) = k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),X0_51) ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_9198,c_34]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_14075,plain,
% 6.79/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 6.79/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.79/1.49      inference(demodulation,[status(thm)],[c_14074,c_9203]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_13,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.79/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.79/1.49      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 6.79/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.79/1.49      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 6.79/1.49      | ~ v1_funct_1(X0)
% 6.79/1.49      | ~ v1_funct_1(X3)
% 6.79/1.49      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 6.79/1.49      | v1_xboole_0(X5)
% 6.79/1.49      | v1_xboole_0(X2)
% 6.79/1.49      | v1_xboole_0(X4)
% 6.79/1.49      | v1_xboole_0(X1)
% 6.79/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.79/1.49      inference(cnf_transformation,[],[f73]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_168,plain,
% 6.79/1.49      ( ~ v1_funct_1(X3)
% 6.79/1.49      | ~ v1_funct_1(X0)
% 6.79/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.79/1.49      | ~ v1_funct_2(X0,X1,X2)
% 6.79/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.79/1.49      | v1_xboole_0(X5)
% 6.79/1.49      | v1_xboole_0(X2)
% 6.79/1.49      | v1_xboole_0(X4)
% 6.79/1.49      | v1_xboole_0(X1)
% 6.79/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_13,c_16,c_15,c_14]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_169,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.79/1.49      | ~ v1_funct_2(X3,X4,X2)
% 6.79/1.49      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 6.79/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.79/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 6.79/1.49      | ~ v1_funct_1(X0)
% 6.79/1.49      | ~ v1_funct_1(X3)
% 6.79/1.49      | v1_xboole_0(X1)
% 6.79/1.49      | v1_xboole_0(X2)
% 6.79/1.49      | v1_xboole_0(X4)
% 6.79/1.49      | v1_xboole_0(X5)
% 6.79/1.49      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 6.79/1.49      inference(renaming,[status(thm)],[c_168]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_837,plain,
% 6.79/1.49      ( ~ v1_funct_2(X0_51,X1_51,X2_51)
% 6.79/1.49      | ~ v1_funct_2(X3_51,X4_51,X2_51)
% 6.79/1.49      | ~ m1_subset_1(X4_51,k1_zfmisc_1(X5_51))
% 6.79/1.49      | ~ m1_subset_1(X1_51,k1_zfmisc_1(X5_51))
% 6.79/1.49      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_51,X2_51)))
% 6.79/1.49      | ~ m1_subset_1(X3_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X2_51)))
% 6.79/1.49      | ~ v1_funct_1(X0_51)
% 6.79/1.49      | ~ v1_funct_1(X3_51)
% 6.79/1.49      | v1_xboole_0(X1_51)
% 6.79/1.49      | v1_xboole_0(X2_51)
% 6.79/1.49      | v1_xboole_0(X4_51)
% 6.79/1.49      | v1_xboole_0(X5_51)
% 6.79/1.49      | k2_partfun1(X1_51,X2_51,X0_51,k9_subset_1(X5_51,X4_51,X1_51)) != k2_partfun1(X4_51,X2_51,X3_51,k9_subset_1(X5_51,X4_51,X1_51))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X5_51,X4_51,X1_51),X2_51,k1_tmap_1(X5_51,X2_51,X4_51,X1_51,X3_51,X0_51),X4_51) = X3_51 ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_169]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1349,plain,
% 6.79/1.49      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X4_51,X0_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X4_51,X0_51))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X3_51,X4_51,X0_51),X1_51,k1_tmap_1(X3_51,X1_51,X4_51,X0_51,X5_51,X2_51),X4_51) = X5_51
% 6.79/1.49      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 6.79/1.49      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 6.79/1.49      | v1_funct_1(X2_51) != iProver_top
% 6.79/1.49      | v1_funct_1(X5_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X3_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X4_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_837]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1523,plain,
% 6.79/1.49      ( k2_partfun1(X0_51,X1_51,X2_51,k9_subset_1(X3_51,X0_51,X4_51)) != k2_partfun1(X4_51,X1_51,X5_51,k9_subset_1(X3_51,X0_51,X4_51))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X3_51,X0_51,X4_51),X1_51,k1_tmap_1(X3_51,X1_51,X0_51,X4_51,X2_51,X5_51),X0_51) = X2_51
% 6.79/1.49      | v1_funct_2(X5_51,X4_51,X1_51) != iProver_top
% 6.79/1.49      | v1_funct_2(X2_51,X0_51,X1_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X4_51,k1_zfmisc_1(X3_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X5_51,k1_zfmisc_1(k2_zfmisc_1(X4_51,X1_51))) != iProver_top
% 6.79/1.49      | m1_subset_1(X2_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 6.79/1.49      | v1_funct_1(X5_51) != iProver_top
% 6.79/1.49      | v1_funct_1(X2_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X1_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(X4_51) = iProver_top ),
% 6.79/1.49      inference(forward_subsumption_resolution,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_1349,c_1330]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_4287,plain,
% 6.79/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),sK2) = sK4
% 6.79/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.79/1.49      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | v1_funct_1(X1_51) != iProver_top
% 6.79/1.49      | v1_funct_1(sK4) != iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top
% 6.79/1.49      | v1_xboole_0(sK1) = iProver_top
% 6.79/1.49      | v1_xboole_0(sK2) = iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_2816,c_1523]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11509,plain,
% 6.79/1.49      ( v1_funct_1(X1_51) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.79/1.49      | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),sK2) = sK4
% 6.79/1.49      | k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_4287,c_32,c_33,c_38,c_39,c_40]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11510,plain,
% 6.79/1.49      ( k2_partfun1(X0_51,sK1,X1_51,k9_subset_1(X2_51,sK2,X0_51)) != k7_relat_1(sK4,k9_subset_1(X2_51,sK2,X0_51))
% 6.79/1.49      | k2_partfun1(k4_subset_1(X2_51,sK2,X0_51),sK1,k1_tmap_1(X2_51,sK1,sK2,X0_51,sK4,X1_51),sK2) = sK4
% 6.79/1.49      | v1_funct_2(X1_51,X0_51,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | m1_subset_1(X1_51,k1_zfmisc_1(k2_zfmisc_1(X0_51,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(X2_51)) != iProver_top
% 6.79/1.49      | v1_funct_1(X1_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(X0_51) = iProver_top ),
% 6.79/1.49      inference(renaming,[status(thm)],[c_11509]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11531,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4
% 6.79/1.49      | k2_partfun1(sK3,sK1,X0_51,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_2534,c_11510]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11628,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4
% 6.79/1.49      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X0_51,k1_xboole_0)
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.79/1.49      inference(light_normalisation,[status(thm)],[c_11531,c_832]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11629,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4
% 6.79/1.49      | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k7_relat_1(sK4,k3_xboole_0(sK2,sK3))
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.79/1.49      inference(demodulation,[status(thm)],[c_11628,c_2534]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11630,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4
% 6.79/1.49      | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | m1_subset_1(sK3,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | m1_subset_1(sK2,k1_zfmisc_1(sK0)) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.79/1.49      inference(light_normalisation,[status(thm)],[c_11629,c_832,c_2482]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11898,plain,
% 6.79/1.49      ( v1_funct_1(X0_51) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
% 6.79/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4 ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_11630,c_34,c_35,c_36]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11899,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X0_51),sK2) = sK4
% 6.79/1.49      | k2_partfun1(sK3,sK1,X0_51,k1_xboole_0) != k1_xboole_0
% 6.79/1.49      | v1_funct_2(X0_51,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_1(X0_51) != iProver_top ),
% 6.79/1.49      inference(renaming,[status(thm)],[c_11898]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11909,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.79/1.49      | k7_relat_1(sK5,k1_xboole_0) != k1_xboole_0
% 6.79/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.79/1.49      inference(superposition,[status(thm)],[c_2811,c_11899]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11910,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.79/1.49      | k1_xboole_0 != k1_xboole_0
% 6.79/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.79/1.49      inference(light_normalisation,[status(thm)],[c_11909,c_2479]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11911,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.79/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.79/1.49      inference(equality_resolution_simp,[status(thm)],[c_11910]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_11912,plain,
% 6.79/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 6.79/1.49      | v1_funct_2(sK5,sK3,sK1) != iProver_top
% 6.79/1.49      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) != iProver_top
% 6.79/1.49      | v1_funct_1(sK5) != iProver_top ),
% 6.79/1.49      inference(demodulation,[status(thm)],[c_11911,c_9203]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_17,negated_conjecture,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.79/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.79/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 6.79/1.49      inference(cnf_transformation,[],[f69]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_850,negated_conjecture,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.79/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.79/1.49      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 6.79/1.49      inference(subtyping,[status(esa)],[c_17]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2666,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.79/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.79/1.49      | k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) ),
% 6.79/1.49      inference(demodulation,[status(thm)],[c_2534,c_850]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2667,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.79/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.79/1.49      | k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) ),
% 6.79/1.49      inference(light_normalisation,[status(thm)],[c_2666,c_832]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2908,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.79/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.79/1.49      | k7_relat_1(sK4,k1_xboole_0) != k1_xboole_0 ),
% 6.79/1.49      inference(demodulation,[status(thm)],[c_2667,c_2479,c_2811,c_2816]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1663,plain,
% 6.79/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 6.79/1.49      | v1_relat_1(sK4) ),
% 6.79/1.49      inference(instantiation,[status(thm)],[c_856]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_1828,plain,
% 6.79/1.49      ( ~ v1_relat_1(sK4) | k7_relat_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 6.79/1.49      inference(instantiation,[status(thm)],[c_831]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2912,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.79/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 6.79/1.49      inference(global_propositional_subsumption,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_2908,c_21,c_1663,c_1828]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_2913,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.79/1.49      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 6.79/1.49      inference(renaming,[status(thm)],[c_2912]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_9207,plain,
% 6.79/1.49      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 6.79/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 ),
% 6.79/1.49      inference(demodulation,[status(thm)],[c_9203,c_2913]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_9208,plain,
% 6.79/1.49      ( k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 6.79/1.49      | k7_relat_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 ),
% 6.79/1.49      inference(demodulation,[status(thm)],[c_9207,c_9203]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(c_43,plain,
% 6.79/1.49      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) = iProver_top ),
% 6.79/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.79/1.49  
% 6.79/1.49  cnf(contradiction,plain,
% 6.79/1.49      ( $false ),
% 6.79/1.49      inference(minisat,
% 6.79/1.49                [status(thm)],
% 6.79/1.49                [c_14075,c_11912,c_9208,c_43,c_42,c_41]) ).
% 6.79/1.49  
% 6.79/1.49  
% 6.79/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.79/1.49  
% 6.79/1.49  ------                               Statistics
% 6.79/1.49  
% 6.79/1.49  ------ General
% 6.79/1.49  
% 6.79/1.49  abstr_ref_over_cycles:                  0
% 6.79/1.49  abstr_ref_under_cycles:                 0
% 6.79/1.49  gc_basic_clause_elim:                   0
% 6.79/1.49  forced_gc_time:                         0
% 6.79/1.49  parsing_time:                           0.009
% 6.79/1.49  unif_index_cands_time:                  0.
% 6.79/1.49  unif_index_add_time:                    0.
% 6.79/1.49  orderings_time:                         0.
% 6.79/1.49  out_proof_time:                         0.016
% 6.79/1.49  total_time:                             0.748
% 6.79/1.49  num_of_symbols:                         56
% 6.79/1.49  num_of_terms:                           28439
% 6.79/1.49  
% 6.79/1.49  ------ Preprocessing
% 6.79/1.49  
% 6.79/1.49  num_of_splits:                          0
% 6.79/1.49  num_of_split_atoms:                     0
% 6.79/1.49  num_of_reused_defs:                     0
% 6.79/1.49  num_eq_ax_congr_red:                    12
% 6.79/1.49  num_of_sem_filtered_clauses:            1
% 6.79/1.49  num_of_subtypes:                        2
% 6.79/1.49  monotx_restored_types:                  0
% 6.79/1.49  sat_num_of_epr_types:                   0
% 6.79/1.49  sat_num_of_non_cyclic_types:            0
% 6.79/1.49  sat_guarded_non_collapsed_types:        1
% 6.79/1.49  num_pure_diseq_elim:                    0
% 6.79/1.49  simp_replaced_by:                       0
% 6.79/1.49  res_preprocessed:                       149
% 6.79/1.49  prep_upred:                             0
% 6.79/1.49  prep_unflattend:                        13
% 6.79/1.49  smt_new_axioms:                         0
% 6.79/1.49  pred_elim_cands:                        5
% 6.79/1.49  pred_elim:                              2
% 6.79/1.49  pred_elim_cl:                           2
% 6.79/1.49  pred_elim_cycles:                       5
% 6.79/1.49  merged_defs:                            2
% 6.79/1.49  merged_defs_ncl:                        0
% 6.79/1.49  bin_hyper_res:                          2
% 6.79/1.49  prep_cycles:                            4
% 6.79/1.49  pred_elim_time:                         0.005
% 6.79/1.49  splitting_time:                         0.
% 6.79/1.49  sem_filter_time:                        0.
% 6.79/1.49  monotx_time:                            0.
% 6.79/1.49  subtype_inf_time:                       0.001
% 6.79/1.49  
% 6.79/1.49  ------ Problem properties
% 6.79/1.49  
% 6.79/1.49  clauses:                                29
% 6.79/1.49  conjectures:                            13
% 6.79/1.49  epr:                                    8
% 6.79/1.49  horn:                                   23
% 6.79/1.49  ground:                                 14
% 6.79/1.49  unary:                                  14
% 6.79/1.49  binary:                                 3
% 6.79/1.49  lits:                                   122
% 6.79/1.49  lits_eq:                                20
% 6.79/1.49  fd_pure:                                0
% 6.79/1.49  fd_pseudo:                              0
% 6.79/1.49  fd_cond:                                0
% 6.79/1.49  fd_pseudo_cond:                         0
% 6.79/1.49  ac_symbols:                             0
% 6.79/1.49  
% 6.79/1.49  ------ Propositional Solver
% 6.79/1.49  
% 6.79/1.49  prop_solver_calls:                      28
% 6.79/1.49  prop_fast_solver_calls:                 2312
% 6.79/1.49  smt_solver_calls:                       0
% 6.79/1.49  smt_fast_solver_calls:                  0
% 6.79/1.49  prop_num_of_clauses:                    5515
% 6.79/1.49  prop_preprocess_simplified:             10683
% 6.79/1.49  prop_fo_subsumed:                       169
% 6.79/1.49  prop_solver_time:                       0.
% 6.79/1.49  smt_solver_time:                        0.
% 6.79/1.49  smt_fast_solver_time:                   0.
% 6.79/1.49  prop_fast_solver_time:                  0.
% 6.79/1.49  prop_unsat_core_time:                   0.
% 6.79/1.49  
% 6.79/1.49  ------ QBF
% 6.79/1.49  
% 6.79/1.49  qbf_q_res:                              0
% 6.79/1.49  qbf_num_tautologies:                    0
% 6.79/1.49  qbf_prep_cycles:                        0
% 6.79/1.49  
% 6.79/1.49  ------ BMC1
% 6.79/1.49  
% 6.79/1.49  bmc1_current_bound:                     -1
% 6.79/1.49  bmc1_last_solved_bound:                 -1
% 6.79/1.49  bmc1_unsat_core_size:                   -1
% 6.79/1.49  bmc1_unsat_core_parents_size:           -1
% 6.79/1.49  bmc1_merge_next_fun:                    0
% 6.79/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.79/1.49  
% 6.79/1.49  ------ Instantiation
% 6.79/1.49  
% 6.79/1.49  inst_num_of_clauses:                    1211
% 6.79/1.49  inst_num_in_passive:                    328
% 6.79/1.49  inst_num_in_active:                     489
% 6.79/1.49  inst_num_in_unprocessed:                394
% 6.79/1.49  inst_num_of_loops:                      600
% 6.79/1.49  inst_num_of_learning_restarts:          0
% 6.79/1.49  inst_num_moves_active_passive:          108
% 6.79/1.49  inst_lit_activity:                      0
% 6.79/1.49  inst_lit_activity_moves:                1
% 6.79/1.49  inst_num_tautologies:                   0
% 6.79/1.49  inst_num_prop_implied:                  0
% 6.79/1.49  inst_num_existing_simplified:           0
% 6.79/1.49  inst_num_eq_res_simplified:             0
% 6.79/1.49  inst_num_child_elim:                    0
% 6.79/1.49  inst_num_of_dismatching_blockings:      165
% 6.79/1.49  inst_num_of_non_proper_insts:           839
% 6.79/1.49  inst_num_of_duplicates:                 0
% 6.79/1.49  inst_inst_num_from_inst_to_res:         0
% 6.79/1.49  inst_dismatching_checking_time:         0.
% 6.79/1.49  
% 6.79/1.49  ------ Resolution
% 6.79/1.49  
% 6.79/1.49  res_num_of_clauses:                     0
% 6.79/1.49  res_num_in_passive:                     0
% 6.79/1.49  res_num_in_active:                      0
% 6.79/1.49  res_num_of_loops:                       153
% 6.79/1.49  res_forward_subset_subsumed:            31
% 6.79/1.49  res_backward_subset_subsumed:           0
% 6.79/1.49  res_forward_subsumed:                   0
% 6.79/1.49  res_backward_subsumed:                  0
% 6.79/1.49  res_forward_subsumption_resolution:     0
% 6.79/1.49  res_backward_subsumption_resolution:    0
% 6.79/1.49  res_clause_to_clause_subsumption:       1320
% 6.79/1.49  res_orphan_elimination:                 0
% 6.79/1.49  res_tautology_del:                      27
% 6.79/1.49  res_num_eq_res_simplified:              0
% 6.79/1.49  res_num_sel_changes:                    0
% 6.79/1.49  res_moves_from_active_to_pass:          0
% 6.79/1.49  
% 6.79/1.49  ------ Superposition
% 6.79/1.49  
% 6.79/1.49  sup_time_total:                         0.
% 6.79/1.49  sup_time_generating:                    0.
% 6.79/1.49  sup_time_sim_full:                      0.
% 6.79/1.49  sup_time_sim_immed:                     0.
% 6.79/1.49  
% 6.79/1.49  sup_num_of_clauses:                     236
% 6.79/1.49  sup_num_in_active:                      116
% 6.79/1.49  sup_num_in_passive:                     120
% 6.79/1.49  sup_num_of_loops:                       119
% 6.79/1.49  sup_fw_superposition:                   208
% 6.79/1.49  sup_bw_superposition:                   58
% 6.79/1.49  sup_immediate_simplified:               131
% 6.79/1.49  sup_given_eliminated:                   0
% 6.79/1.49  comparisons_done:                       0
% 6.79/1.49  comparisons_avoided:                    0
% 6.79/1.49  
% 6.79/1.49  ------ Simplifications
% 6.79/1.49  
% 6.79/1.49  
% 6.79/1.49  sim_fw_subset_subsumed:                 7
% 6.79/1.49  sim_bw_subset_subsumed:                 0
% 6.79/1.49  sim_fw_subsumed:                        14
% 6.79/1.49  sim_bw_subsumed:                        8
% 6.79/1.49  sim_fw_subsumption_res:                 9
% 6.79/1.49  sim_bw_subsumption_res:                 0
% 6.79/1.49  sim_tautology_del:                      0
% 6.79/1.49  sim_eq_tautology_del:                   9
% 6.79/1.49  sim_eq_res_simp:                        4
% 6.79/1.49  sim_fw_demodulated:                     74
% 6.79/1.49  sim_bw_demodulated:                     4
% 6.79/1.49  sim_light_normalised:                   41
% 6.79/1.49  sim_joinable_taut:                      0
% 6.79/1.49  sim_joinable_simp:                      0
% 6.79/1.49  sim_ac_normalised:                      0
% 6.79/1.49  sim_smt_subsumption:                    0
% 6.79/1.49  
%------------------------------------------------------------------------------
