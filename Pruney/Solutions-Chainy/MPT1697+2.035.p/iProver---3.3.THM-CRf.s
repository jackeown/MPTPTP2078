%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:21:29 EST 2020

% Result     : Theorem 11.29s
% Output     : CNFRefutation 11.29s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 694 expanded)
%              Number of clauses        :  101 ( 218 expanded)
%              Number of leaves         :   24 ( 250 expanded)
%              Depth                    :   22
%              Number of atoms          : 1063 (7347 expanded)
%              Number of equality atoms :  201 (1582 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal clause size      :   32 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f31])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,(
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

fof(f41,plain,
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

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f32,f46,f45,f44,f43,f42,f41])).

fof(f85,plain,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f73,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f80,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f83,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f47])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f27])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f29])).

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
    inference(cnf_transformation,[],[f30])).

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
    inference(cnf_transformation,[],[f30])).

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
    inference(cnf_transformation,[],[f30])).

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
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
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

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_682,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4688,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X3 != k7_relat_1(X0,X4)
    | k2_partfun1(X1,X2,X0,X4) = X3 ),
    inference(resolution,[status(thm)],[c_17,c_682])).

cnf(c_24,negated_conjecture,
    ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_19406,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_4688,c_24])).

cnf(c_37,negated_conjecture,
    ( ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_35,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,negated_conjecture,
    ( ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_20,plain,
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
    inference(cnf_transformation,[],[f91])).

cnf(c_23,plain,
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

cnf(c_22,plain,
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

cnf(c_21,plain,
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

cnf(c_394,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_23,c_22,c_21])).

cnf(c_395,plain,
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
    inference(renaming,[status(thm)],[c_394])).

cnf(c_2087,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK4,k9_subset_1(X4,X3,X1))
    | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK4,X0),X3) = sK4 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_2372,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ v1_funct_2(sK4,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | k2_partfun1(X0,X1,sK5,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK4,k9_subset_1(X3,X2,X0))
    | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK4,sK5),X2) = sK4 ),
    inference(instantiation,[status(thm)],[c_2087])).

cnf(c_3236,plain,
    ( ~ v1_funct_2(sK5,X0,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | k2_partfun1(X0,sK1,sK5,k9_subset_1(X1,sK2,X0)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1,sK2,X0))
    | k2_partfun1(k4_subset_1(X1,sK2,X0),sK1,k1_tmap_1(X1,sK1,sK2,X0,sK4,sK5),sK2) = sK4 ),
    inference(instantiation,[status(thm)],[c_2372])).

cnf(c_4203,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3236])).

cnf(c_6091,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4203])).

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
    | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_403,plain,
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
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_23,c_22,c_21])).

cnf(c_404,plain,
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
    inference(renaming,[status(thm)],[c_403])).

cnf(c_2097,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK4,X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4)
    | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK4,k9_subset_1(X4,X3,X1))
    | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK4,X0),X1) = X0 ),
    inference(instantiation,[status(thm)],[c_404])).

cnf(c_2390,plain,
    ( ~ v1_funct_2(sK5,X0,X1)
    | ~ v1_funct_2(sK4,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(X3)
    | k2_partfun1(X0,X1,sK5,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK4,k9_subset_1(X3,X2,X0))
    | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK4,sK5),X0) = sK5 ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_3327,plain,
    ( ~ v1_funct_2(sK5,X0,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | k2_partfun1(X0,sK1,sK5,k9_subset_1(X1,sK2,X0)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1,sK2,X0))
    | k2_partfun1(k4_subset_1(X1,sK2,X0),sK1,k1_tmap_1(X1,sK1,sK2,X0,sK4,sK5),X0) = sK5 ),
    inference(instantiation,[status(thm)],[c_2390])).

cnf(c_4231,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3327])).

cnf(c_6168,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4231])).

cnf(c_10234,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != X0
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_682])).

cnf(c_13310,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_10234])).

cnf(c_2019,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2238,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2019])).

cnf(c_13311,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_2238])).

cnf(c_19750,plain,
    ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19406,c_37,c_36,c_35,c_34,c_33,c_32,c_30,c_29,c_28,c_27,c_26,c_25,c_6091,c_6168,c_13310,c_13311])).

cnf(c_19760,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_19750,c_4688])).

cnf(c_19846,plain,
    ( k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19760,c_27,c_25])).

cnf(c_681,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3593,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_682,c_681])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3710,plain,
    ( ~ v1_xboole_0(X0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3593,c_3])).

cnf(c_3730,plain,
    ( ~ v1_xboole_0(X0)
    | X0 = X1
    | X1 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3710,c_682])).

cnf(c_8597,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(resolution,[status(thm)],[c_3730,c_3710])).

cnf(c_19853,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)))
    | ~ v1_xboole_0(k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_19846,c_8597])).

cnf(c_12,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_684,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_29379,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k7_relat_1(X0,X1))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_684])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_29989,plain,
    ( v1_xboole_0(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ r1_xboole_0(k1_relat_1(X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_29379,c_2])).

cnf(c_29990,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(k7_relat_1(X0,X1)) ),
    inference(renaming,[status(thm)],[c_29989])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_237,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_238,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_237])).

cnf(c_319,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_238])).

cnf(c_8913,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X2,X0) = k9_subset_1(X1,X2,X0) ),
    inference(resolution,[status(thm)],[c_319,c_3593])).

cnf(c_13201,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(k9_subset_1(X1,X2,X0))
    | v1_xboole_0(k3_xboole_0(X2,X0)) ),
    inference(resolution,[status(thm)],[c_8913,c_684])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_318,plain,
    ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_238])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8641,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_subset_1(X1,X2,X0),X1) ),
    inference(resolution,[status(thm)],[c_318,c_11])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_320,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_238])).

cnf(c_10179,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k9_subset_1(X1,X2,X0)) ),
    inference(resolution,[status(thm)],[c_8641,c_320])).

cnf(c_28713,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k3_xboole_0(X2,X0)) ),
    inference(resolution,[status(thm)],[c_13201,c_10179])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_28726,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k3_xboole_0(X1,X0)) ),
    inference(resolution,[status(thm)],[c_28713,c_6])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3721,plain,
    ( r1_xboole_0(X0,X1)
    | ~ v1_xboole_0(k3_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_3710,c_0])).

cnf(c_29075,plain,
    ( r1_xboole_0(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_28726,c_3721])).

cnf(c_30535,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(k7_relat_1(X0,X1)) ),
    inference(resolution,[status(thm)],[c_29990,c_29075])).

cnf(c_31610,plain,
    ( ~ v1_relat_1(sK5)
    | ~ v1_xboole_0(k9_subset_1(sK0,sK2,sK3))
    | ~ v1_xboole_0(k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))) ),
    inference(resolution,[status(thm)],[c_19853,c_30535])).

cnf(c_31,negated_conjecture,
    ( r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1943,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( ~ r1_subset_1(X0,X1)
    | r1_xboole_0(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1993,plain,
    ( ~ r1_subset_1(sK2,sK3)
    | r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2161,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1954,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_2454,plain,
    ( v1_xboole_0(k3_xboole_0(sK2,sK3))
    | ~ v1_xboole_0(k1_xboole_0)
    | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1954])).

cnf(c_1504,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1522,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2777,plain,
    ( r1_tarski(sK3,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1522])).

cnf(c_1497,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_6235,plain,
    ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_2777,c_1497])).

cnf(c_6250,plain,
    ( k9_subset_1(sK0,sK2,sK3) = k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_6235])).

cnf(c_3532,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
    | X0 != k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_5256,plain,
    ( v1_xboole_0(k9_subset_1(X0,sK2,sK3))
    | ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
    | k9_subset_1(X0,sK2,sK3) != k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3532])).

cnf(c_12699,plain,
    ( v1_xboole_0(k9_subset_1(sK0,sK2,sK3))
    | ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
    | k9_subset_1(sK0,sK2,sK3) != k3_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_5256])).

cnf(c_32049,plain,
    ( ~ v1_xboole_0(k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31610,c_35,c_33,c_31,c_25,c_2,c_1943,c_1993,c_2161,c_2454,c_6250,c_12699])).

cnf(c_32061,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_xboole_0(k9_subset_1(sK0,sK2,sK3)) ),
    inference(resolution,[status(thm)],[c_32049,c_30535])).

cnf(c_1946,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_32061,c_12699,c_6250,c_2454,c_2161,c_1993,c_1946,c_2,c_28,c_31,c_33,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:50:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.29/2.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.29/2.03  
% 11.29/2.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.29/2.03  
% 11.29/2.03  ------  iProver source info
% 11.29/2.03  
% 11.29/2.03  git: date: 2020-06-30 10:37:57 +0100
% 11.29/2.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.29/2.03  git: non_committed_changes: false
% 11.29/2.03  git: last_make_outside_of_git: false
% 11.29/2.03  
% 11.29/2.03  ------ 
% 11.29/2.03  ------ Parsing...
% 11.29/2.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.29/2.03  
% 11.29/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.29/2.03  
% 11.29/2.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.29/2.03  
% 11.29/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.29/2.03  ------ Proving...
% 11.29/2.03  ------ Problem Properties 
% 11.29/2.03  
% 11.29/2.03  
% 11.29/2.03  clauses                                 37
% 11.29/2.03  conjectures                             14
% 11.29/2.03  EPR                                     16
% 11.29/2.03  Horn                                    29
% 11.29/2.03  unary                                   15
% 11.29/2.03  binary                                  8
% 11.29/2.03  lits                                    141
% 11.29/2.03  lits eq                                 17
% 11.29/2.03  fd_pure                                 0
% 11.29/2.03  fd_pseudo                               0
% 11.29/2.03  fd_cond                                 1
% 11.29/2.03  fd_pseudo_cond                          1
% 11.29/2.03  AC symbols                              0
% 11.29/2.03  
% 11.29/2.03  ------ Input Options Time Limit: Unbounded
% 11.29/2.03  
% 11.29/2.03  
% 11.29/2.03  ------ 
% 11.29/2.03  Current options:
% 11.29/2.03  ------ 
% 11.29/2.03  
% 11.29/2.03  
% 11.29/2.03  
% 11.29/2.03  
% 11.29/2.03  ------ Proving...
% 11.29/2.03  
% 11.29/2.03  
% 11.29/2.03  % SZS status Theorem for theBenchmark.p
% 11.29/2.03  
% 11.29/2.03  % SZS output start CNFRefutation for theBenchmark.p
% 11.29/2.03  
% 11.29/2.03  fof(f12,axiom,(
% 11.29/2.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f25,plain,(
% 11.29/2.03    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.29/2.03    inference(ennf_transformation,[],[f12])).
% 11.29/2.03  
% 11.29/2.03  fof(f26,plain,(
% 11.29/2.03    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.29/2.03    inference(flattening,[],[f25])).
% 11.29/2.03  
% 11.29/2.03  fof(f65,plain,(
% 11.29/2.03    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f26])).
% 11.29/2.03  
% 11.29/2.03  fof(f15,conjecture,(
% 11.29/2.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f16,negated_conjecture,(
% 11.29/2.03    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 11.29/2.03    inference(negated_conjecture,[],[f15])).
% 11.29/2.03  
% 11.29/2.03  fof(f31,plain,(
% 11.29/2.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.29/2.03    inference(ennf_transformation,[],[f16])).
% 11.29/2.03  
% 11.29/2.03  fof(f32,plain,(
% 11.29/2.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 11.29/2.03    inference(flattening,[],[f31])).
% 11.29/2.03  
% 11.29/2.03  fof(f46,plain,(
% 11.29/2.03    ( ! [X4,X2,X0,X3,X1] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X3) != sK5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,sK5),X2) != X4 | k2_partfun1(X3,X1,sK5,k9_subset_1(X0,X2,X3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(sK5,X3,X1) & v1_funct_1(sK5))) )),
% 11.29/2.03    introduced(choice_axiom,[])).
% 11.29/2.03  
% 11.29/2.03  fof(f45,plain,(
% 11.29/2.03    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,sK4,X5),X2) != sK4 | k2_partfun1(X2,X1,sK4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(sK4,X2,X1) & v1_funct_1(sK4))) )),
% 11.29/2.03    introduced(choice_axiom,[])).
% 11.29/2.03  
% 11.29/2.03  fof(f44,plain,(
% 11.29/2.03    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(X0,X2,sK3),X1,k1_tmap_1(X0,X1,X2,sK3,X4,X5),X2) != X4 | k2_partfun1(sK3,X1,X5,k9_subset_1(X0,X2,sK3)) != k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) & v1_funct_2(X5,sK3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK3))) )),
% 11.29/2.03    introduced(choice_axiom,[])).
% 11.29/2.03  
% 11.29/2.03  fof(f43,plain,(
% 11.29/2.03    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,sK2,X3),X1,k1_tmap_1(X0,X1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,X1,X4,k9_subset_1(X0,sK2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,X1))) & v1_funct_2(X4,sK2,X1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(X0)) & ~v1_xboole_0(sK2))) )),
% 11.29/2.03    introduced(choice_axiom,[])).
% 11.29/2.03  
% 11.29/2.03  fof(f42,plain,(
% 11.29/2.03    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),sK1,k1_tmap_1(X0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))) )),
% 11.29/2.03    introduced(choice_axiom,[])).
% 11.29/2.03  
% 11.29/2.03  fof(f41,plain,(
% 11.29/2.03    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 11.29/2.03    introduced(choice_axiom,[])).
% 11.29/2.03  
% 11.29/2.03  fof(f47,plain,(
% 11.29/2.03    ((((((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 11.29/2.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f32,f46,f45,f44,f43,f42,f41])).
% 11.29/2.03  
% 11.29/2.03  fof(f85,plain,(
% 11.29/2.03    k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f72,plain,(
% 11.29/2.03    ~v1_xboole_0(sK0)),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f73,plain,(
% 11.29/2.03    ~v1_xboole_0(sK1)),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f74,plain,(
% 11.29/2.03    ~v1_xboole_0(sK2)),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f75,plain,(
% 11.29/2.03    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f76,plain,(
% 11.29/2.03    ~v1_xboole_0(sK3)),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f77,plain,(
% 11.29/2.03    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f79,plain,(
% 11.29/2.03    v1_funct_1(sK4)),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f80,plain,(
% 11.29/2.03    v1_funct_2(sK4,sK2,sK1)),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f81,plain,(
% 11.29/2.03    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f82,plain,(
% 11.29/2.03    v1_funct_1(sK5)),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f83,plain,(
% 11.29/2.03    v1_funct_2(sK5,sK3,sK1)),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f84,plain,(
% 11.29/2.03    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f13,axiom,(
% 11.29/2.03    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f27,plain,(
% 11.29/2.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.29/2.03    inference(ennf_transformation,[],[f13])).
% 11.29/2.03  
% 11.29/2.03  fof(f28,plain,(
% 11.29/2.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.29/2.03    inference(flattening,[],[f27])).
% 11.29/2.03  
% 11.29/2.03  fof(f39,plain,(
% 11.29/2.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.29/2.03    inference(nnf_transformation,[],[f28])).
% 11.29/2.03  
% 11.29/2.03  fof(f40,plain,(
% 11.29/2.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 11.29/2.03    inference(flattening,[],[f39])).
% 11.29/2.03  
% 11.29/2.03  fof(f66,plain,(
% 11.29/2.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f40])).
% 11.29/2.03  
% 11.29/2.03  fof(f91,plain,(
% 11.29/2.03    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.29/2.03    inference(equality_resolution,[],[f66])).
% 11.29/2.03  
% 11.29/2.03  fof(f14,axiom,(
% 11.29/2.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f29,plain,(
% 11.29/2.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.29/2.03    inference(ennf_transformation,[],[f14])).
% 11.29/2.03  
% 11.29/2.03  fof(f30,plain,(
% 11.29/2.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.29/2.03    inference(flattening,[],[f29])).
% 11.29/2.03  
% 11.29/2.03  fof(f69,plain,(
% 11.29/2.03    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f30])).
% 11.29/2.03  
% 11.29/2.03  fof(f70,plain,(
% 11.29/2.03    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f30])).
% 11.29/2.03  
% 11.29/2.03  fof(f71,plain,(
% 11.29/2.03    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f30])).
% 11.29/2.03  
% 11.29/2.03  fof(f67,plain,(
% 11.29/2.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f40])).
% 11.29/2.03  
% 11.29/2.03  fof(f90,plain,(
% 11.29/2.03    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.29/2.03    inference(equality_resolution,[],[f67])).
% 11.29/2.03  
% 11.29/2.03  fof(f3,axiom,(
% 11.29/2.03    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f17,plain,(
% 11.29/2.03    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 11.29/2.03    inference(ennf_transformation,[],[f3])).
% 11.29/2.03  
% 11.29/2.03  fof(f51,plain,(
% 11.29/2.03    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f17])).
% 11.29/2.03  
% 11.29/2.03  fof(f9,axiom,(
% 11.29/2.03    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f21,plain,(
% 11.29/2.03    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.29/2.03    inference(ennf_transformation,[],[f9])).
% 11.29/2.03  
% 11.29/2.03  fof(f37,plain,(
% 11.29/2.03    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.29/2.03    inference(nnf_transformation,[],[f21])).
% 11.29/2.03  
% 11.29/2.03  fof(f61,plain,(
% 11.29/2.03    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f37])).
% 11.29/2.03  
% 11.29/2.03  fof(f2,axiom,(
% 11.29/2.03    v1_xboole_0(k1_xboole_0)),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f50,plain,(
% 11.29/2.03    v1_xboole_0(k1_xboole_0)),
% 11.29/2.03    inference(cnf_transformation,[],[f2])).
% 11.29/2.03  
% 11.29/2.03  fof(f6,axiom,(
% 11.29/2.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f19,plain,(
% 11.29/2.03    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.29/2.03    inference(ennf_transformation,[],[f6])).
% 11.29/2.03  
% 11.29/2.03  fof(f56,plain,(
% 11.29/2.03    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.29/2.03    inference(cnf_transformation,[],[f19])).
% 11.29/2.03  
% 11.29/2.03  fof(f8,axiom,(
% 11.29/2.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f36,plain,(
% 11.29/2.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.29/2.03    inference(nnf_transformation,[],[f8])).
% 11.29/2.03  
% 11.29/2.03  fof(f59,plain,(
% 11.29/2.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f36])).
% 11.29/2.03  
% 11.29/2.03  fof(f5,axiom,(
% 11.29/2.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f18,plain,(
% 11.29/2.03    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.29/2.03    inference(ennf_transformation,[],[f5])).
% 11.29/2.03  
% 11.29/2.03  fof(f55,plain,(
% 11.29/2.03    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.29/2.03    inference(cnf_transformation,[],[f18])).
% 11.29/2.03  
% 11.29/2.03  fof(f58,plain,(
% 11.29/2.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.29/2.03    inference(cnf_transformation,[],[f36])).
% 11.29/2.03  
% 11.29/2.03  fof(f7,axiom,(
% 11.29/2.03    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f20,plain,(
% 11.29/2.03    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 11.29/2.03    inference(ennf_transformation,[],[f7])).
% 11.29/2.03  
% 11.29/2.03  fof(f57,plain,(
% 11.29/2.03    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f20])).
% 11.29/2.03  
% 11.29/2.03  fof(f4,axiom,(
% 11.29/2.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f34,plain,(
% 11.29/2.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.29/2.03    inference(nnf_transformation,[],[f4])).
% 11.29/2.03  
% 11.29/2.03  fof(f35,plain,(
% 11.29/2.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.29/2.03    inference(flattening,[],[f34])).
% 11.29/2.03  
% 11.29/2.03  fof(f52,plain,(
% 11.29/2.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.29/2.03    inference(cnf_transformation,[],[f35])).
% 11.29/2.03  
% 11.29/2.03  fof(f87,plain,(
% 11.29/2.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.29/2.03    inference(equality_resolution,[],[f52])).
% 11.29/2.03  
% 11.29/2.03  fof(f1,axiom,(
% 11.29/2.03    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f33,plain,(
% 11.29/2.03    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 11.29/2.03    inference(nnf_transformation,[],[f1])).
% 11.29/2.03  
% 11.29/2.03  fof(f49,plain,(
% 11.29/2.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 11.29/2.03    inference(cnf_transformation,[],[f33])).
% 11.29/2.03  
% 11.29/2.03  fof(f78,plain,(
% 11.29/2.03    r1_subset_1(sK2,sK3)),
% 11.29/2.03    inference(cnf_transformation,[],[f47])).
% 11.29/2.03  
% 11.29/2.03  fof(f11,axiom,(
% 11.29/2.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f24,plain,(
% 11.29/2.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.29/2.03    inference(ennf_transformation,[],[f11])).
% 11.29/2.03  
% 11.29/2.03  fof(f64,plain,(
% 11.29/2.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.29/2.03    inference(cnf_transformation,[],[f24])).
% 11.29/2.03  
% 11.29/2.03  fof(f10,axiom,(
% 11.29/2.03    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 11.29/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.29/2.03  
% 11.29/2.03  fof(f22,plain,(
% 11.29/2.03    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.29/2.03    inference(ennf_transformation,[],[f10])).
% 11.29/2.03  
% 11.29/2.03  fof(f23,plain,(
% 11.29/2.03    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.29/2.03    inference(flattening,[],[f22])).
% 11.29/2.03  
% 11.29/2.03  fof(f38,plain,(
% 11.29/2.03    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.29/2.03    inference(nnf_transformation,[],[f23])).
% 11.29/2.03  
% 11.29/2.03  fof(f62,plain,(
% 11.29/2.03    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f38])).
% 11.29/2.03  
% 11.29/2.03  fof(f48,plain,(
% 11.29/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 11.29/2.03    inference(cnf_transformation,[],[f33])).
% 11.29/2.03  
% 11.29/2.03  cnf(c_17,plain,
% 11.29/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | k2_partfun1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 11.29/2.03      inference(cnf_transformation,[],[f65]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_682,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_4688,plain,
% 11.29/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | X3 != k7_relat_1(X0,X4)
% 11.29/2.03      | k2_partfun1(X1,X2,X0,X4) = X3 ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_17,c_682]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_24,negated_conjecture,
% 11.29/2.03      ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.29/2.03      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.29/2.03      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.29/2.03      inference(cnf_transformation,[],[f85]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_19406,plain,
% 11.29/2.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) != sK5
% 11.29/2.03      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) != sK4
% 11.29/2.03      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_4688,c_24]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_37,negated_conjecture,
% 11.29/2.03      ( ~ v1_xboole_0(sK0) ),
% 11.29/2.03      inference(cnf_transformation,[],[f72]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_36,negated_conjecture,
% 11.29/2.03      ( ~ v1_xboole_0(sK1) ),
% 11.29/2.03      inference(cnf_transformation,[],[f73]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_35,negated_conjecture,
% 11.29/2.03      ( ~ v1_xboole_0(sK2) ),
% 11.29/2.03      inference(cnf_transformation,[],[f74]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_34,negated_conjecture,
% 11.29/2.03      ( m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
% 11.29/2.03      inference(cnf_transformation,[],[f75]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_33,negated_conjecture,
% 11.29/2.03      ( ~ v1_xboole_0(sK3) ),
% 11.29/2.03      inference(cnf_transformation,[],[f76]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_32,negated_conjecture,
% 11.29/2.03      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
% 11.29/2.03      inference(cnf_transformation,[],[f77]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_30,negated_conjecture,
% 11.29/2.03      ( v1_funct_1(sK4) ),
% 11.29/2.03      inference(cnf_transformation,[],[f79]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_29,negated_conjecture,
% 11.29/2.03      ( v1_funct_2(sK4,sK2,sK1) ),
% 11.29/2.03      inference(cnf_transformation,[],[f80]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_28,negated_conjecture,
% 11.29/2.03      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 11.29/2.03      inference(cnf_transformation,[],[f81]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_27,negated_conjecture,
% 11.29/2.03      ( v1_funct_1(sK5) ),
% 11.29/2.03      inference(cnf_transformation,[],[f82]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_26,negated_conjecture,
% 11.29/2.03      ( v1_funct_2(sK5,sK3,sK1) ),
% 11.29/2.03      inference(cnf_transformation,[],[f83]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_25,negated_conjecture,
% 11.29/2.03      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
% 11.29/2.03      inference(cnf_transformation,[],[f84]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_20,plain,
% 11.29/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ v1_funct_2(X3,X4,X2)
% 11.29/2.03      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.29/2.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.29/2.03      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_1(X3)
% 11.29/2.03      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.29/2.03      | v1_xboole_0(X5)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.29/2.03      inference(cnf_transformation,[],[f91]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_23,plain,
% 11.29/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ v1_funct_2(X3,X4,X2)
% 11.29/2.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_1(X3)
% 11.29/2.03      | v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.29/2.03      | v1_xboole_0(X5)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | v1_xboole_0(X1) ),
% 11.29/2.03      inference(cnf_transformation,[],[f69]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_22,plain,
% 11.29/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ v1_funct_2(X3,X4,X2)
% 11.29/2.03      | v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.29/2.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_1(X3)
% 11.29/2.03      | v1_xboole_0(X5)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | v1_xboole_0(X1) ),
% 11.29/2.03      inference(cnf_transformation,[],[f70]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_21,plain,
% 11.29/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ v1_funct_2(X3,X4,X2)
% 11.29/2.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.29/2.03      | m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_1(X3)
% 11.29/2.03      | v1_xboole_0(X5)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | v1_xboole_0(X1) ),
% 11.29/2.03      inference(cnf_transformation,[],[f71]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_394,plain,
% 11.29/2.03      ( ~ v1_funct_1(X3)
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_2(X3,X4,X2)
% 11.29/2.03      | ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.29/2.03      | v1_xboole_0(X5)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.29/2.03      inference(global_propositional_subsumption,
% 11.29/2.03                [status(thm)],
% 11.29/2.03                [c_20,c_23,c_22,c_21]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_395,plain,
% 11.29/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ v1_funct_2(X3,X4,X2)
% 11.29/2.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_1(X3)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | v1_xboole_0(X5)
% 11.29/2.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X4) = X3 ),
% 11.29/2.03      inference(renaming,[status(thm)],[c_394]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_2087,plain,
% 11.29/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ v1_funct_2(sK4,X3,X2)
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X3)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK4,k9_subset_1(X4,X3,X1))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK4,X0),X3) = sK4 ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_395]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_2372,plain,
% 11.29/2.03      ( ~ v1_funct_2(sK5,X0,X1)
% 11.29/2.03      | ~ v1_funct_2(sK4,X2,X1)
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 11.29/2.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 11.29/2.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.29/2.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.29/2.03      | ~ v1_funct_1(sK5)
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | v1_xboole_0(X0)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X3)
% 11.29/2.03      | k2_partfun1(X0,X1,sK5,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK4,k9_subset_1(X3,X2,X0))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK4,sK5),X2) = sK4 ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_2087]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_3236,plain,
% 11.29/2.03      ( ~ v1_funct_2(sK5,X0,sK1)
% 11.29/2.03      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.29/2.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
% 11.29/2.03      | ~ v1_funct_1(sK5)
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | v1_xboole_0(X0)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(sK1)
% 11.29/2.03      | v1_xboole_0(sK2)
% 11.29/2.03      | k2_partfun1(X0,sK1,sK5,k9_subset_1(X1,sK2,X0)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1,sK2,X0))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X1,sK2,X0),sK1,k1_tmap_1(X1,sK1,sK2,X0,sK4,sK5),sK2) = sK4 ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_2372]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_4203,plain,
% 11.29/2.03      ( ~ v1_funct_2(sK5,sK3,sK1)
% 11.29/2.03      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.29/2.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 11.29/2.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 11.29/2.03      | ~ v1_funct_1(sK5)
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | v1_xboole_0(X0)
% 11.29/2.03      | v1_xboole_0(sK1)
% 11.29/2.03      | v1_xboole_0(sK3)
% 11.29/2.03      | v1_xboole_0(sK2)
% 11.29/2.03      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.29/2.03      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,sK3)) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_3236]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_6091,plain,
% 11.29/2.03      ( ~ v1_funct_2(sK5,sK3,sK1)
% 11.29/2.03      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.29/2.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 11.29/2.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 11.29/2.03      | ~ v1_funct_1(sK5)
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | v1_xboole_0(sK1)
% 11.29/2.03      | v1_xboole_0(sK3)
% 11.29/2.03      | v1_xboole_0(sK2)
% 11.29/2.03      | v1_xboole_0(sK0)
% 11.29/2.03      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) = sK4
% 11.29/2.03      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_4203]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_19,plain,
% 11.29/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ v1_funct_2(X3,X4,X2)
% 11.29/2.03      | ~ v1_funct_2(k1_tmap_1(X5,X2,X4,X1,X3,X0),k4_subset_1(X5,X4,X1),X2)
% 11.29/2.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.29/2.03      | ~ m1_subset_1(k1_tmap_1(X5,X2,X4,X1,X3,X0),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X5,X4,X1),X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_1(X3)
% 11.29/2.03      | ~ v1_funct_1(k1_tmap_1(X5,X2,X4,X1,X3,X0))
% 11.29/2.03      | v1_xboole_0(X5)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.29/2.03      inference(cnf_transformation,[],[f90]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_403,plain,
% 11.29/2.03      ( ~ v1_funct_1(X3)
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_2(X3,X4,X2)
% 11.29/2.03      | ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.29/2.03      | v1_xboole_0(X5)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.29/2.03      inference(global_propositional_subsumption,
% 11.29/2.03                [status(thm)],
% 11.29/2.03                [c_19,c_23,c_22,c_21]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_404,plain,
% 11.29/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ v1_funct_2(X3,X4,X2)
% 11.29/2.03      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X5))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_1(X3)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | v1_xboole_0(X5)
% 11.29/2.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X5,X4,X1)) != k2_partfun1(X4,X2,X3,k9_subset_1(X5,X4,X1))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X5,X4,X1),X2,k1_tmap_1(X5,X2,X4,X1,X3,X0),X1) = X0 ),
% 11.29/2.03      inference(renaming,[status(thm)],[c_403]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_2097,plain,
% 11.29/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.29/2.03      | ~ v1_funct_2(sK4,X3,X2)
% 11.29/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
% 11.29/2.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 11.29/2.03      | ~ v1_funct_1(X0)
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X3)
% 11.29/2.03      | v1_xboole_0(X4)
% 11.29/2.03      | k2_partfun1(X1,X2,X0,k9_subset_1(X4,X3,X1)) != k2_partfun1(X3,X2,sK4,k9_subset_1(X4,X3,X1))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X4,X3,X1),X2,k1_tmap_1(X4,X2,X3,X1,sK4,X0),X1) = X0 ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_404]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_2390,plain,
% 11.29/2.03      ( ~ v1_funct_2(sK5,X0,X1)
% 11.29/2.03      | ~ v1_funct_2(sK4,X2,X1)
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
% 11.29/2.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 11.29/2.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.29/2.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.29/2.03      | ~ v1_funct_1(sK5)
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | v1_xboole_0(X0)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(X2)
% 11.29/2.03      | v1_xboole_0(X3)
% 11.29/2.03      | k2_partfun1(X0,X1,sK5,k9_subset_1(X3,X2,X0)) != k2_partfun1(X2,X1,sK4,k9_subset_1(X3,X2,X0))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X3,X2,X0),X1,k1_tmap_1(X3,X1,X2,X0,sK4,sK5),X0) = sK5 ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_2097]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_3327,plain,
% 11.29/2.03      ( ~ v1_funct_2(sK5,X0,sK1)
% 11.29/2.03      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.29/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.29/2.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(X1))
% 11.29/2.03      | ~ v1_funct_1(sK5)
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | v1_xboole_0(X0)
% 11.29/2.03      | v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(sK1)
% 11.29/2.03      | v1_xboole_0(sK2)
% 11.29/2.03      | k2_partfun1(X0,sK1,sK5,k9_subset_1(X1,sK2,X0)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X1,sK2,X0))
% 11.29/2.03      | k2_partfun1(k4_subset_1(X1,sK2,X0),sK1,k1_tmap_1(X1,sK1,sK2,X0,sK4,sK5),X0) = sK5 ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_2390]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_4231,plain,
% 11.29/2.03      ( ~ v1_funct_2(sK5,sK3,sK1)
% 11.29/2.03      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.29/2.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 11.29/2.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 11.29/2.03      | ~ v1_funct_1(sK5)
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | v1_xboole_0(X0)
% 11.29/2.03      | v1_xboole_0(sK1)
% 11.29/2.03      | v1_xboole_0(sK3)
% 11.29/2.03      | v1_xboole_0(sK2)
% 11.29/2.03      | k2_partfun1(k4_subset_1(X0,sK2,sK3),sK1,k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.29/2.03      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(X0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,sK3)) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_3327]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_6168,plain,
% 11.29/2.03      ( ~ v1_funct_2(sK5,sK3,sK1)
% 11.29/2.03      | ~ v1_funct_2(sK4,sK2,sK1)
% 11.29/2.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.29/2.03      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
% 11.29/2.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
% 11.29/2.03      | ~ v1_funct_1(sK5)
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | v1_xboole_0(sK1)
% 11.29/2.03      | v1_xboole_0(sK3)
% 11.29/2.03      | v1_xboole_0(sK2)
% 11.29/2.03      | v1_xboole_0(sK0)
% 11.29/2.03      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) = sK5
% 11.29/2.03      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_4231]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_10234,plain,
% 11.29/2.03      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != X0
% 11.29/2.03      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
% 11.29/2.03      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != X0 ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_682]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_13310,plain,
% 11.29/2.03      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
% 11.29/2.03      | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
% 11.29/2.03      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_10234]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_2019,plain,
% 11.29/2.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_17]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_2238,plain,
% 11.29/2.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_2019]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_13311,plain,
% 11.29/2.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.29/2.03      | ~ v1_funct_1(sK4)
% 11.29/2.03      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_2238]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_19750,plain,
% 11.29/2.03      ( k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
% 11.29/2.03      inference(global_propositional_subsumption,
% 11.29/2.03                [status(thm)],
% 11.29/2.03                [c_19406,c_37,c_36,c_35,c_34,c_33,c_32,c_30,c_29,c_28,
% 11.29/2.03                 c_27,c_26,c_25,c_6091,c_6168,c_13310,c_13311]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_19760,plain,
% 11.29/2.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.29/2.03      | ~ v1_funct_1(sK5)
% 11.29/2.03      | k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_19750,c_4688]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_19846,plain,
% 11.29/2.03      ( k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
% 11.29/2.03      inference(global_propositional_subsumption,
% 11.29/2.03                [status(thm)],
% 11.29/2.03                [c_19760,c_27,c_25]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_681,plain,( X0 = X0 ),theory(equality) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_3593,plain,
% 11.29/2.03      ( X0 != X1 | X1 = X0 ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_682,c_681]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_3,plain,
% 11.29/2.03      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 11.29/2.03      inference(cnf_transformation,[],[f51]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_3710,plain,
% 11.29/2.03      ( ~ v1_xboole_0(X0) | X0 = k1_xboole_0 ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_3593,c_3]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_3730,plain,
% 11.29/2.03      ( ~ v1_xboole_0(X0) | X0 = X1 | X1 != k1_xboole_0 ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_3710,c_682]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_8597,plain,
% 11.29/2.03      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_3730,c_3710]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_19853,plain,
% 11.29/2.03      ( ~ v1_xboole_0(k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)))
% 11.29/2.03      | ~ v1_xboole_0(k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_19846,c_8597]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_12,plain,
% 11.29/2.03      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.29/2.03      | ~ v1_relat_1(X0)
% 11.29/2.03      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 11.29/2.03      inference(cnf_transformation,[],[f61]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_684,plain,
% 11.29/2.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 11.29/2.03      theory(equality) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_29379,plain,
% 11.29/2.03      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.29/2.03      | ~ v1_relat_1(X0)
% 11.29/2.03      | v1_xboole_0(k7_relat_1(X0,X1))
% 11.29/2.03      | ~ v1_xboole_0(k1_xboole_0) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_12,c_684]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_2,plain,
% 11.29/2.03      ( v1_xboole_0(k1_xboole_0) ),
% 11.29/2.03      inference(cnf_transformation,[],[f50]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_29989,plain,
% 11.29/2.03      ( v1_xboole_0(k7_relat_1(X0,X1))
% 11.29/2.03      | ~ v1_relat_1(X0)
% 11.29/2.03      | ~ r1_xboole_0(k1_relat_1(X0),X1) ),
% 11.29/2.03      inference(global_propositional_subsumption,
% 11.29/2.03                [status(thm)],
% 11.29/2.03                [c_29379,c_2]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_29990,plain,
% 11.29/2.03      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 11.29/2.03      | ~ v1_relat_1(X0)
% 11.29/2.03      | v1_xboole_0(k7_relat_1(X0,X1)) ),
% 11.29/2.03      inference(renaming,[status(thm)],[c_29989]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_8,plain,
% 11.29/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.29/2.03      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 11.29/2.03      inference(cnf_transformation,[],[f56]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_10,plain,
% 11.29/2.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.29/2.03      inference(cnf_transformation,[],[f59]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_237,plain,
% 11.29/2.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.29/2.03      inference(prop_impl,[status(thm)],[c_10]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_238,plain,
% 11.29/2.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.29/2.03      inference(renaming,[status(thm)],[c_237]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_319,plain,
% 11.29/2.03      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 11.29/2.03      inference(bin_hyper_res,[status(thm)],[c_8,c_238]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_8913,plain,
% 11.29/2.03      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X2,X0) = k9_subset_1(X1,X2,X0) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_319,c_3593]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_13201,plain,
% 11.29/2.03      ( ~ r1_tarski(X0,X1)
% 11.29/2.03      | ~ v1_xboole_0(k9_subset_1(X1,X2,X0))
% 11.29/2.03      | v1_xboole_0(k3_xboole_0(X2,X0)) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_8913,c_684]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_7,plain,
% 11.29/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.29/2.03      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 11.29/2.03      inference(cnf_transformation,[],[f55]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_318,plain,
% 11.29/2.03      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 11.29/2.03      | ~ r1_tarski(X2,X0) ),
% 11.29/2.03      inference(bin_hyper_res,[status(thm)],[c_7,c_238]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_11,plain,
% 11.29/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.29/2.03      inference(cnf_transformation,[],[f58]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_8641,plain,
% 11.29/2.03      ( ~ r1_tarski(X0,X1) | r1_tarski(k9_subset_1(X1,X2,X0),X1) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_318,c_11]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_9,plain,
% 11.29/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.29/2.03      | ~ v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(X0) ),
% 11.29/2.03      inference(cnf_transformation,[],[f57]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_320,plain,
% 11.29/2.03      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 11.29/2.03      inference(bin_hyper_res,[status(thm)],[c_9,c_238]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_10179,plain,
% 11.29/2.03      ( ~ r1_tarski(X0,X1)
% 11.29/2.03      | ~ v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(k9_subset_1(X1,X2,X0)) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_8641,c_320]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_28713,plain,
% 11.29/2.03      ( ~ r1_tarski(X0,X1)
% 11.29/2.03      | ~ v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(k3_xboole_0(X2,X0)) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_13201,c_10179]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_6,plain,
% 11.29/2.03      ( r1_tarski(X0,X0) ),
% 11.29/2.03      inference(cnf_transformation,[],[f87]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_28726,plain,
% 11.29/2.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(k3_xboole_0(X1,X0)) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_28713,c_6]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_0,plain,
% 11.29/2.03      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 11.29/2.03      inference(cnf_transformation,[],[f49]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_3721,plain,
% 11.29/2.03      ( r1_xboole_0(X0,X1) | ~ v1_xboole_0(k3_xboole_0(X0,X1)) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_3710,c_0]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_29075,plain,
% 11.29/2.03      ( r1_xboole_0(X0,X1) | ~ v1_xboole_0(X1) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_28726,c_3721]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_30535,plain,
% 11.29/2.03      ( ~ v1_relat_1(X0)
% 11.29/2.03      | ~ v1_xboole_0(X1)
% 11.29/2.03      | v1_xboole_0(k7_relat_1(X0,X1)) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_29990,c_29075]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_31610,plain,
% 11.29/2.03      ( ~ v1_relat_1(sK5)
% 11.29/2.03      | ~ v1_xboole_0(k9_subset_1(sK0,sK2,sK3))
% 11.29/2.03      | ~ v1_xboole_0(k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_19853,c_30535]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_31,negated_conjecture,
% 11.29/2.03      ( r1_subset_1(sK2,sK3) ),
% 11.29/2.03      inference(cnf_transformation,[],[f78]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_16,plain,
% 11.29/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.29/2.03      | v1_relat_1(X0) ),
% 11.29/2.03      inference(cnf_transformation,[],[f64]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_1943,plain,
% 11.29/2.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
% 11.29/2.03      | v1_relat_1(sK5) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_16]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_15,plain,
% 11.29/2.03      ( ~ r1_subset_1(X0,X1)
% 11.29/2.03      | r1_xboole_0(X0,X1)
% 11.29/2.03      | v1_xboole_0(X0)
% 11.29/2.03      | v1_xboole_0(X1) ),
% 11.29/2.03      inference(cnf_transformation,[],[f62]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_1993,plain,
% 11.29/2.03      ( ~ r1_subset_1(sK2,sK3)
% 11.29/2.03      | r1_xboole_0(sK2,sK3)
% 11.29/2.03      | v1_xboole_0(sK3)
% 11.29/2.03      | v1_xboole_0(sK2) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_15]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_1,plain,
% 11.29/2.03      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.29/2.03      inference(cnf_transformation,[],[f48]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_2161,plain,
% 11.29/2.03      ( ~ r1_xboole_0(sK2,sK3) | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_1]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_1954,plain,
% 11.29/2.03      ( v1_xboole_0(X0)
% 11.29/2.03      | ~ v1_xboole_0(k1_xboole_0)
% 11.29/2.03      | X0 != k1_xboole_0 ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_684]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_2454,plain,
% 11.29/2.03      ( v1_xboole_0(k3_xboole_0(sK2,sK3))
% 11.29/2.03      | ~ v1_xboole_0(k1_xboole_0)
% 11.29/2.03      | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_1954]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_1504,plain,
% 11.29/2.03      ( m1_subset_1(sK3,k1_zfmisc_1(sK0)) = iProver_top ),
% 11.29/2.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_1522,plain,
% 11.29/2.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.29/2.03      | r1_tarski(X0,X1) = iProver_top ),
% 11.29/2.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_2777,plain,
% 11.29/2.03      ( r1_tarski(sK3,sK0) = iProver_top ),
% 11.29/2.03      inference(superposition,[status(thm)],[c_1504,c_1522]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_1497,plain,
% 11.29/2.03      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 11.29/2.03      | r1_tarski(X2,X0) != iProver_top ),
% 11.29/2.03      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_6235,plain,
% 11.29/2.03      ( k9_subset_1(sK0,X0,sK3) = k3_xboole_0(X0,sK3) ),
% 11.29/2.03      inference(superposition,[status(thm)],[c_2777,c_1497]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_6250,plain,
% 11.29/2.03      ( k9_subset_1(sK0,sK2,sK3) = k3_xboole_0(sK2,sK3) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_6235]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_3532,plain,
% 11.29/2.03      ( v1_xboole_0(X0)
% 11.29/2.03      | ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
% 11.29/2.03      | X0 != k3_xboole_0(sK2,sK3) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_684]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_5256,plain,
% 11.29/2.03      ( v1_xboole_0(k9_subset_1(X0,sK2,sK3))
% 11.29/2.03      | ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
% 11.29/2.03      | k9_subset_1(X0,sK2,sK3) != k3_xboole_0(sK2,sK3) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_3532]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_12699,plain,
% 11.29/2.03      ( v1_xboole_0(k9_subset_1(sK0,sK2,sK3))
% 11.29/2.03      | ~ v1_xboole_0(k3_xboole_0(sK2,sK3))
% 11.29/2.03      | k9_subset_1(sK0,sK2,sK3) != k3_xboole_0(sK2,sK3) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_5256]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_32049,plain,
% 11.29/2.03      ( ~ v1_xboole_0(k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))) ),
% 11.29/2.03      inference(global_propositional_subsumption,
% 11.29/2.03                [status(thm)],
% 11.29/2.03                [c_31610,c_35,c_33,c_31,c_25,c_2,c_1943,c_1993,c_2161,
% 11.29/2.03                 c_2454,c_6250,c_12699]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_32061,plain,
% 11.29/2.03      ( ~ v1_relat_1(sK4) | ~ v1_xboole_0(k9_subset_1(sK0,sK2,sK3)) ),
% 11.29/2.03      inference(resolution,[status(thm)],[c_32049,c_30535]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(c_1946,plain,
% 11.29/2.03      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 11.29/2.03      | v1_relat_1(sK4) ),
% 11.29/2.03      inference(instantiation,[status(thm)],[c_16]) ).
% 11.29/2.03  
% 11.29/2.03  cnf(contradiction,plain,
% 11.29/2.03      ( $false ),
% 11.29/2.03      inference(minisat,
% 11.29/2.03                [status(thm)],
% 11.29/2.03                [c_32061,c_12699,c_6250,c_2454,c_2161,c_1993,c_1946,c_2,
% 11.29/2.03                 c_28,c_31,c_33,c_35]) ).
% 11.29/2.03  
% 11.29/2.03  
% 11.29/2.03  % SZS output end CNFRefutation for theBenchmark.p
% 11.29/2.03  
% 11.29/2.03  ------                               Statistics
% 11.29/2.03  
% 11.29/2.03  ------ Selected
% 11.29/2.03  
% 11.29/2.03  total_time:                             1.261
% 11.29/2.03  
%------------------------------------------------------------------------------
