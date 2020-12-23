%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:33 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 945 expanded)
%              Number of leaves         :   20 ( 432 expanded)
%              Depth                    :   27
%              Number of atoms          :  945 (13369 expanded)
%              Number of equality atoms :  206 (2980 expanded)
%              Maximal formula depth    :   25 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f449,plain,(
    $false ),
    inference(global_subsumption,[],[f163,f392,f448])).

fof(f448,plain,(
    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f447,f55])).

fof(f55,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
      | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f37,f36,f35,f34,f33,f32])).

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

% (7886)Termination reason: Refutation not found, incomplete strategy

% (7886)Memory used [KB]: 2174
% (7886)Time elapsed: 0.173 s
% (7886)------------------------------
% (7886)------------------------------
fof(f33,plain,
    ( ? [X1] :
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
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5
                        | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4
                        | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                      & v1_funct_2(X5,X3,sK1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                  & v1_funct_2(X4,X2,sK1)
                  & v1_funct_1(X4) )
              & r1_subset_1(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4
                      | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                    & v1_funct_2(X5,X3,sK1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                & v1_funct_2(X4,X2,sK1)
                & v1_funct_1(X4) )
            & r1_subset_1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(sK0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5
                    | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4
                    | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                  & v1_funct_2(X5,X3,sK1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
              & v1_funct_2(X4,sK2,sK1)
              & v1_funct_1(X4) )
          & r1_subset_1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5
                  | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4
                  | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                & v1_funct_2(X5,X3,sK1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
            & v1_funct_2(X4,sK2,sK1)
            & v1_funct_1(X4) )
        & r1_subset_1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5
                | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4
                | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_2(X5,sK3,sK1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X4,sK2,sK1)
          & v1_funct_1(X4) )
      & r1_subset_1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5
              | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4
              | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
            & v1_funct_2(X5,sK3,sK1)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        & v1_funct_2(X4,sK2,sK1)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5
            | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2)
            | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
          & v1_funct_2(X5,sK3,sK1)
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & v1_funct_2(sK4,sK2,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X5] :
        ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5
          | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2)
          | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        & v1_funct_2(X5,sK3,sK1)
        & v1_funct_1(X5) )
   => ( ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
        | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
        | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      & v1_funct_2(sK5,sK3,sK1)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f447,plain,
    ( sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subsumption_resolution,[],[f446,f53])).

fof(f53,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f446,plain,
    ( ~ v1_funct_1(sK5)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subsumption_resolution,[],[f445,f54])).

fof(f54,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f445,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subsumption_resolution,[],[f444,f106])).

fof(f106,plain,(
    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    inference(resolution,[],[f97,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f97,plain,(
    v1_xboole_0(k7_relat_1(sK5,k1_xboole_0)) ),
    inference(resolution,[],[f95,f93])).

fof(f93,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f66,f55])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_xboole_0(k7_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f74,f70])).

fof(f70,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f444,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(superposition,[],[f443,f161])).

fof(f161,plain,(
    ! [X0] : k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0) ),
    inference(resolution,[],[f157,f55])).

fof(f157,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k2_partfun1(X3,X4,sK5,X5) = k7_relat_1(sK5,X5) ) ),
    inference(resolution,[],[f65,f53])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f443,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_partfun1(sK3,sK1,X1,k1_xboole_0)
      | ~ v1_funct_2(X1,sK3,sK1)
      | ~ v1_funct_1(X1)
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ) ),
    inference(forward_demodulation,[],[f442,f100])).

fof(f100,plain,(
    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    inference(resolution,[],[f96,f64])).

fof(f96,plain,(
    v1_xboole_0(k7_relat_1(sK4,k1_xboole_0)) ),
    inference(resolution,[],[f95,f92])).

fof(f92,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f66,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f442,plain,(
    ! [X1] :
      ( k7_relat_1(sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,X1,k1_xboole_0)
      | ~ v1_funct_2(X1,sK3,sK1)
      | ~ v1_funct_1(X1)
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ) ),
    inference(forward_demodulation,[],[f441,f145])).

fof(f145,plain,(
    k1_xboole_0 = k9_subset_1(sK0,sK2,sK3) ),
    inference(superposition,[],[f141,f137])).

fof(f137,plain,(
    k1_xboole_0 = k1_setfam_1(k1_enumset1(sK2,sK2,sK3)) ),
    inference(resolution,[],[f80,f134])).

fof(f134,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f133,f45])).

fof(f45,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f133,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f132,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f67,f49])).

fof(f49,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,X1)) ) ),
    inference(definition_unfolding,[],[f71,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f76])).

fof(f76,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f141,plain,(
    ! [X1] : k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k1_enumset1(X1,X1,sK3)) ),
    inference(resolution,[],[f78,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f63,f77])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f441,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,sK3,sK1)
      | ~ v1_funct_1(X1)
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | k2_partfun1(sK3,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f439,f47])).

fof(f439,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,sK3,sK1)
      | ~ v1_funct_1(X1)
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | v1_xboole_0(sK3)
      | k2_partfun1(sK3,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ) ),
    inference(resolution,[],[f437,f48])).

fof(f437,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ v1_funct_2(X0,X1,sK1)
      | ~ v1_funct_1(X0)
      | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X1),sK1,k1_tmap_1(sK0,sK1,sK2,X1,sK4,X0),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | v1_xboole_0(X1)
      | k2_partfun1(X1,sK1,X0,k9_subset_1(sK0,sK2,X1)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X1)) ) ),
    inference(resolution,[],[f428,f46])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f428,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,X1)) ) ),
    inference(forward_demodulation,[],[f427,f158])).

fof(f158,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    inference(resolution,[],[f156,f52])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2) ) ),
    inference(resolution,[],[f65,f50])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f427,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f426,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f426,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f425,f44])).

fof(f44,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f425,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f424,f45])).

fof(f424,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f423,f50])).

fof(f423,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f419,f52])).

fof(f419,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f90,f51])).

fof(f51,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X4,X2,X1)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f89,f58])).

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
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
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
    inference(subsumption_resolution,[],[f88,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
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
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
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
    inference(subsumption_resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f392,plain,(
    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(subsumption_resolution,[],[f391,f55])).

fof(f391,plain,
    ( sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subsumption_resolution,[],[f390,f53])).

fof(f390,plain,
    ( ~ v1_funct_1(sK5)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subsumption_resolution,[],[f389,f54])).

fof(f389,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(subsumption_resolution,[],[f388,f106])).

fof(f388,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(superposition,[],[f387,f161])).

fof(f387,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_partfun1(sK3,sK1,X1,k1_xboole_0)
      | ~ v1_funct_2(X1,sK3,sK1)
      | ~ v1_funct_1(X1)
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK3) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ) ),
    inference(forward_demodulation,[],[f386,f100])).

fof(f386,plain,(
    ! [X1] :
      ( k7_relat_1(sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,X1,k1_xboole_0)
      | ~ v1_funct_2(X1,sK3,sK1)
      | ~ v1_funct_1(X1)
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK3) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ) ),
    inference(forward_demodulation,[],[f385,f145])).

fof(f385,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,sK3,sK1)
      | ~ v1_funct_1(X1)
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK3) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | k2_partfun1(sK3,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ) ),
    inference(subsumption_resolution,[],[f383,f47])).

fof(f383,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,sK3,sK1)
      | ~ v1_funct_1(X1)
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK3) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      | v1_xboole_0(sK3)
      | k2_partfun1(sK3,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ) ),
    inference(resolution,[],[f381,f48])).

fof(f381,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ v1_funct_2(X0,X1,sK1)
      | ~ v1_funct_1(X0)
      | k2_partfun1(k4_subset_1(sK0,sK2,X1),sK1,k1_tmap_1(sK0,sK1,sK2,X1,sK4,X0),X1) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | v1_xboole_0(X1)
      | k2_partfun1(X1,sK1,X0,k9_subset_1(sK0,sK2,X1)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X1)) ) ),
    inference(resolution,[],[f372,f46])).

fof(f372,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,X1)) ) ),
    inference(forward_demodulation,[],[f371,f158])).

fof(f371,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f370,f69])).

fof(f370,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f369,f44])).

fof(f369,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f368,f45])).

fof(f368,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f367,f50])).

fof(f367,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f363,f52])).

fof(f363,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f87,f51])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X4,X2,X1)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f86,f58])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
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
    inference(subsumption_resolution,[],[f85,f59])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
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
    inference(subsumption_resolution,[],[f83,f57])).

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
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
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

fof(f163,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(subsumption_resolution,[],[f162,f106])).

fof(f162,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(backward_demodulation,[],[f160,f161])).

fof(f160,plain,
    ( k1_xboole_0 != k2_partfun1(sK3,sK1,sK5,k1_xboole_0)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(forward_demodulation,[],[f159,f100])).

fof(f159,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(backward_demodulation,[],[f148,f158])).

fof(f148,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0)
    | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(backward_demodulation,[],[f56,f145])).

fof(f56,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:16:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (7871)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (7872)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (7888)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (7880)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (7870)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (7879)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (7878)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (7889)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (7873)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (7886)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (7867)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (7887)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (7890)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (7891)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (7866)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (7882)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (7868)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (7881)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (7874)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (7875)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (7892)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (7894)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (7884)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (7882)Refutation not found, incomplete strategy% (7882)------------------------------
% 0.21/0.56  % (7882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7882)Memory used [KB]: 10746
% 0.21/0.56  % (7882)Time elapsed: 0.098 s
% 0.21/0.56  % (7882)------------------------------
% 0.21/0.56  % (7882)------------------------------
% 0.21/0.56  % (7869)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (7876)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (7865)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (7883)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % (7887)Refutation not found, incomplete strategy% (7887)------------------------------
% 0.21/0.57  % (7887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7887)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7887)Memory used [KB]: 11385
% 0.21/0.57  % (7887)Time elapsed: 0.128 s
% 0.21/0.57  % (7887)------------------------------
% 0.21/0.57  % (7887)------------------------------
% 0.21/0.57  % (7885)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (7877)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.52/0.57  % (7893)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.52/0.58  % (7870)Refutation found. Thanks to Tanya!
% 1.52/0.58  % SZS status Theorem for theBenchmark
% 1.65/0.59  % (7886)Refutation not found, incomplete strategy% (7886)------------------------------
% 1.65/0.59  % (7886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.61  % (7875)Refutation not found, incomplete strategy% (7875)------------------------------
% 1.65/0.61  % (7875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.61  % SZS output start Proof for theBenchmark
% 1.65/0.61  fof(f449,plain,(
% 1.65/0.61    $false),
% 1.65/0.61    inference(global_subsumption,[],[f163,f392,f448])).
% 1.65/0.61  fof(f448,plain,(
% 1.65/0.61    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.65/0.61    inference(subsumption_resolution,[],[f447,f55])).
% 1.65/0.61  fof(f55,plain,(
% 1.65/0.61    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f38,plain,(
% 1.65/0.61    ((((((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.65/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f37,f36,f35,f34,f33,f32])).
% 1.65/0.61  fof(f32,plain,(
% 1.65/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.65/0.61    introduced(choice_axiom,[])).
% 1.65/0.61  % (7886)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.61  
% 1.65/0.61  % (7886)Memory used [KB]: 2174
% 1.65/0.61  % (7886)Time elapsed: 0.173 s
% 1.65/0.61  % (7886)------------------------------
% 1.65/0.61  % (7886)------------------------------
% 1.65/0.61  fof(f33,plain,(
% 1.65/0.61    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 1.65/0.61    introduced(choice_axiom,[])).
% 1.65/0.61  fof(f34,plain,(
% 1.65/0.61    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2))),
% 1.65/0.61    introduced(choice_axiom,[])).
% 1.65/0.61  fof(f35,plain,(
% 1.65/0.61    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3))),
% 1.65/0.61    introduced(choice_axiom,[])).
% 1.65/0.61  fof(f36,plain,(
% 1.65/0.61    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 1.65/0.61    introduced(choice_axiom,[])).
% 1.65/0.61  fof(f37,plain,(
% 1.65/0.61    ? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) => ((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5))),
% 1.65/0.61    introduced(choice_axiom,[])).
% 1.65/0.61  fof(f17,plain,(
% 1.65/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.65/0.61    inference(flattening,[],[f16])).
% 1.65/0.61  fof(f16,plain,(
% 1.65/0.61    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.65/0.61    inference(ennf_transformation,[],[f15])).
% 1.65/0.61  fof(f15,negated_conjecture,(
% 1.65/0.61    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.65/0.61    inference(negated_conjecture,[],[f14])).
% 1.65/0.61  fof(f14,conjecture,(
% 1.65/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.65/0.61  fof(f447,plain,(
% 1.65/0.61    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.65/0.61    inference(subsumption_resolution,[],[f446,f53])).
% 1.65/0.61  fof(f53,plain,(
% 1.65/0.61    v1_funct_1(sK5)),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f446,plain,(
% 1.65/0.61    ~v1_funct_1(sK5) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.65/0.61    inference(subsumption_resolution,[],[f445,f54])).
% 1.65/0.61  fof(f54,plain,(
% 1.65/0.61    v1_funct_2(sK5,sK3,sK1)),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f445,plain,(
% 1.65/0.61    ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.65/0.61    inference(subsumption_resolution,[],[f444,f106])).
% 1.65/0.61  fof(f106,plain,(
% 1.65/0.61    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 1.65/0.61    inference(resolution,[],[f97,f64])).
% 1.65/0.61  fof(f64,plain,(
% 1.65/0.61    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.65/0.61    inference(cnf_transformation,[],[f23])).
% 1.65/0.61  fof(f23,plain,(
% 1.65/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.65/0.61    inference(ennf_transformation,[],[f3])).
% 1.65/0.61  fof(f3,axiom,(
% 1.65/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.65/0.61  fof(f97,plain,(
% 1.65/0.61    v1_xboole_0(k7_relat_1(sK5,k1_xboole_0))),
% 1.65/0.61    inference(resolution,[],[f95,f93])).
% 1.65/0.61  fof(f93,plain,(
% 1.65/0.61    v1_relat_1(sK5)),
% 1.65/0.61    inference(resolution,[],[f66,f55])).
% 1.65/0.61  fof(f66,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f26])).
% 1.65/0.61  fof(f26,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.61    inference(ennf_transformation,[],[f10])).
% 1.65/0.61  fof(f10,axiom,(
% 1.65/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.65/0.61  fof(f95,plain,(
% 1.65/0.61    ( ! [X0] : (~v1_relat_1(X0) | v1_xboole_0(k7_relat_1(X0,k1_xboole_0))) )),
% 1.65/0.61    inference(resolution,[],[f74,f70])).
% 1.65/0.61  fof(f70,plain,(
% 1.65/0.61    v1_xboole_0(k1_xboole_0)),
% 1.65/0.61    inference(cnf_transformation,[],[f2])).
% 1.65/0.61  fof(f2,axiom,(
% 1.65/0.61    v1_xboole_0(k1_xboole_0)),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.65/0.61  fof(f74,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~v1_xboole_0(X1) | v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f31])).
% 1.65/0.61  fof(f31,plain,(
% 1.65/0.61    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_xboole_0(X1) | ~v1_relat_1(X0))),
% 1.65/0.61    inference(flattening,[],[f30])).
% 1.65/0.61  fof(f30,plain,(
% 1.65/0.61    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_xboole_0(X1) | ~v1_relat_1(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f8])).
% 1.65/0.61  fof(f8,axiom,(
% 1.65/0.61    ! [X0,X1] : ((v1_xboole_0(X1) & v1_relat_1(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).
% 1.65/0.61  fof(f444,plain,(
% 1.65/0.61    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.65/0.61    inference(superposition,[],[f443,f161])).
% 1.65/0.61  fof(f161,plain,(
% 1.65/0.61    ( ! [X0] : (k7_relat_1(sK5,X0) = k2_partfun1(sK3,sK1,sK5,X0)) )),
% 1.65/0.61    inference(resolution,[],[f157,f55])).
% 1.65/0.61  fof(f157,plain,(
% 1.65/0.61    ( ! [X4,X5,X3] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_partfun1(X3,X4,sK5,X5) = k7_relat_1(sK5,X5)) )),
% 1.65/0.61    inference(resolution,[],[f65,f53])).
% 1.65/0.61  fof(f65,plain,(
% 1.65/0.61    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f25])).
% 1.65/0.61  fof(f25,plain,(
% 1.65/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.65/0.61    inference(flattening,[],[f24])).
% 1.65/0.61  fof(f24,plain,(
% 1.65/0.61    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.65/0.61    inference(ennf_transformation,[],[f11])).
% 1.65/0.61  fof(f11,axiom,(
% 1.65/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.65/0.61  fof(f443,plain,(
% 1.65/0.61    ( ! [X1] : (k1_xboole_0 != k2_partfun1(sK3,sK1,X1,k1_xboole_0) | ~v1_funct_2(X1,sK3,sK1) | ~v1_funct_1(X1) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))) )),
% 1.65/0.61    inference(forward_demodulation,[],[f442,f100])).
% 1.65/0.61  fof(f100,plain,(
% 1.65/0.61    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.65/0.61    inference(resolution,[],[f96,f64])).
% 1.65/0.61  fof(f96,plain,(
% 1.65/0.61    v1_xboole_0(k7_relat_1(sK4,k1_xboole_0))),
% 1.65/0.61    inference(resolution,[],[f95,f92])).
% 1.65/0.61  fof(f92,plain,(
% 1.65/0.61    v1_relat_1(sK4)),
% 1.65/0.61    inference(resolution,[],[f66,f52])).
% 1.65/0.61  fof(f52,plain,(
% 1.65/0.61    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f442,plain,(
% 1.65/0.61    ( ! [X1] : (k7_relat_1(sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,X1,k1_xboole_0) | ~v1_funct_2(X1,sK3,sK1) | ~v1_funct_1(X1) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))) )),
% 1.65/0.61    inference(forward_demodulation,[],[f441,f145])).
% 1.65/0.61  fof(f145,plain,(
% 1.65/0.61    k1_xboole_0 = k9_subset_1(sK0,sK2,sK3)),
% 1.65/0.61    inference(superposition,[],[f141,f137])).
% 1.65/0.61  fof(f137,plain,(
% 1.65/0.61    k1_xboole_0 = k1_setfam_1(k1_enumset1(sK2,sK2,sK3))),
% 1.65/0.61    inference(resolution,[],[f80,f134])).
% 1.65/0.61  fof(f134,plain,(
% 1.65/0.61    r1_xboole_0(sK2,sK3)),
% 1.65/0.61    inference(subsumption_resolution,[],[f133,f45])).
% 1.65/0.61  fof(f45,plain,(
% 1.65/0.61    ~v1_xboole_0(sK2)),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f133,plain,(
% 1.65/0.61    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 1.65/0.61    inference(subsumption_resolution,[],[f132,f47])).
% 1.65/0.61  fof(f47,plain,(
% 1.65/0.61    ~v1_xboole_0(sK3)),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f132,plain,(
% 1.65/0.61    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2)),
% 1.65/0.61    inference(resolution,[],[f67,f49])).
% 1.65/0.61  fof(f49,plain,(
% 1.65/0.61    r1_subset_1(sK2,sK3)),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f67,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f41])).
% 1.65/0.61  fof(f41,plain,(
% 1.65/0.61    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.65/0.61    inference(nnf_transformation,[],[f28])).
% 1.65/0.61  fof(f28,plain,(
% 1.65/0.61    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.65/0.61    inference(flattening,[],[f27])).
% 1.65/0.61  fof(f27,plain,(
% 1.65/0.61    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f9])).
% 1.65/0.61  fof(f9,axiom,(
% 1.65/0.61    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.65/0.61  fof(f80,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.65/0.61    inference(definition_unfolding,[],[f71,f77])).
% 1.65/0.61  fof(f77,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.65/0.61    inference(definition_unfolding,[],[f73,f76])).
% 1.65/0.61  fof(f76,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f4])).
% 1.65/0.61  fof(f4,axiom,(
% 1.65/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.65/0.61  fof(f73,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.65/0.61    inference(cnf_transformation,[],[f7])).
% 1.65/0.61  fof(f7,axiom,(
% 1.65/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.65/0.61  fof(f71,plain,(
% 1.65/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f42])).
% 1.65/0.61  fof(f42,plain,(
% 1.65/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.65/0.61    inference(nnf_transformation,[],[f1])).
% 1.65/0.61  fof(f1,axiom,(
% 1.65/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.65/0.61  fof(f141,plain,(
% 1.65/0.61    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k1_setfam_1(k1_enumset1(X1,X1,sK3))) )),
% 1.65/0.61    inference(resolution,[],[f78,f48])).
% 1.65/0.61  fof(f48,plain,(
% 1.65/0.61    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f78,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k1_enumset1(X1,X1,X2))) )),
% 1.65/0.61    inference(definition_unfolding,[],[f63,f77])).
% 1.65/0.61  fof(f63,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.65/0.61    inference(cnf_transformation,[],[f22])).
% 1.65/0.61  fof(f22,plain,(
% 1.65/0.61    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f5])).
% 1.65/0.61  fof(f5,axiom,(
% 1.65/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.65/0.61  fof(f441,plain,(
% 1.65/0.61    ( ! [X1] : (~v1_funct_2(X1,sK3,sK1) | ~v1_funct_1(X1) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK3,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f439,f47])).
% 1.65/0.61  fof(f439,plain,(
% 1.65/0.61    ( ! [X1] : (~v1_funct_2(X1,sK3,sK1) | ~v1_funct_1(X1) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK3) | k2_partfun1(sK3,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))) )),
% 1.65/0.61    inference(resolution,[],[f437,f48])).
% 1.65/0.61  fof(f437,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_2(X0,X1,sK1) | ~v1_funct_1(X0) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,X1),sK1,k1_tmap_1(sK0,sK1,sK2,X1,sK4,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | v1_xboole_0(X1) | k2_partfun1(X1,sK1,X0,k9_subset_1(sK0,sK2,X1)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X1))) )),
% 1.65/0.61    inference(resolution,[],[f428,f46])).
% 1.65/0.61  fof(f46,plain,(
% 1.65/0.61    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f428,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,X1))) )),
% 1.65/0.61    inference(forward_demodulation,[],[f427,f158])).
% 1.65/0.61  fof(f158,plain,(
% 1.65/0.61    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) )),
% 1.65/0.61    inference(resolution,[],[f156,f52])).
% 1.65/0.61  fof(f156,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK4,X2) = k7_relat_1(sK4,X2)) )),
% 1.65/0.61    inference(resolution,[],[f65,f50])).
% 1.65/0.61  fof(f50,plain,(
% 1.65/0.61    v1_funct_1(sK4)),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f427,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f426,f69])).
% 1.65/0.61  fof(f69,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f29])).
% 1.65/0.61  fof(f29,plain,(
% 1.65/0.61    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.65/0.61    inference(ennf_transformation,[],[f6])).
% 1.65/0.61  fof(f6,axiom,(
% 1.65/0.61    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.65/0.61  fof(f426,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f425,f44])).
% 1.65/0.61  fof(f44,plain,(
% 1.65/0.61    ~v1_xboole_0(sK1)),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f425,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f424,f45])).
% 1.65/0.61  fof(f424,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f423,f50])).
% 1.65/0.61  fof(f423,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f419,f52])).
% 1.65/0.61  fof(f419,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),sK2) | ~v1_funct_1(sK4) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(resolution,[],[f90,f51])).
% 1.65/0.61  fof(f51,plain,(
% 1.65/0.61    v1_funct_2(sK4,sK2,sK1)),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  fof(f90,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X4,X2,X1) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f89,f58])).
% 1.65/0.61  fof(f58,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f19])).
% 1.65/0.61  fof(f19,plain,(
% 1.65/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.65/0.61    inference(flattening,[],[f18])).
% 1.65/0.61  fof(f18,plain,(
% 1.65/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.65/0.61    inference(ennf_transformation,[],[f13])).
% 1.65/0.61  fof(f13,axiom,(
% 1.65/0.61    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.65/0.61  fof(f89,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f88,f59])).
% 1.65/0.61  fof(f59,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f19])).
% 1.65/0.61  fof(f88,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f84,f57])).
% 1.65/0.61  fof(f57,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f19])).
% 1.65/0.61  fof(f84,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(equality_resolution,[],[f60])).
% 1.65/0.61  fof(f60,plain,(
% 1.65/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f40])).
% 1.65/0.61  fof(f40,plain,(
% 1.65/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.65/0.61    inference(flattening,[],[f39])).
% 1.65/0.61  fof(f39,plain,(
% 1.65/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.65/0.61    inference(nnf_transformation,[],[f21])).
% 1.65/0.61  fof(f21,plain,(
% 1.65/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.65/0.61    inference(flattening,[],[f20])).
% 1.65/0.61  fof(f20,plain,(
% 1.65/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.65/0.61    inference(ennf_transformation,[],[f12])).
% 1.65/0.61  fof(f12,axiom,(
% 1.65/0.61    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.65/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.65/0.61  fof(f392,plain,(
% 1.65/0.61    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.65/0.61    inference(subsumption_resolution,[],[f391,f55])).
% 1.65/0.61  fof(f391,plain,(
% 1.65/0.61    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.65/0.61    inference(subsumption_resolution,[],[f390,f53])).
% 1.65/0.61  fof(f390,plain,(
% 1.65/0.61    ~v1_funct_1(sK5) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.65/0.61    inference(subsumption_resolution,[],[f389,f54])).
% 1.65/0.61  fof(f389,plain,(
% 1.65/0.61    ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.65/0.61    inference(subsumption_resolution,[],[f388,f106])).
% 1.65/0.61  fof(f388,plain,(
% 1.65/0.61    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.65/0.61    inference(superposition,[],[f387,f161])).
% 1.65/0.61  fof(f387,plain,(
% 1.65/0.61    ( ! [X1] : (k1_xboole_0 != k2_partfun1(sK3,sK1,X1,k1_xboole_0) | ~v1_funct_2(X1,sK3,sK1) | ~v1_funct_1(X1) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK3) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))) )),
% 1.65/0.61    inference(forward_demodulation,[],[f386,f100])).
% 1.65/0.61  fof(f386,plain,(
% 1.65/0.61    ( ! [X1] : (k7_relat_1(sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,X1,k1_xboole_0) | ~v1_funct_2(X1,sK3,sK1) | ~v1_funct_1(X1) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK3) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))) )),
% 1.65/0.61    inference(forward_demodulation,[],[f385,f145])).
% 1.65/0.61  fof(f385,plain,(
% 1.65/0.61    ( ! [X1] : (~v1_funct_2(X1,sK3,sK1) | ~v1_funct_1(X1) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK3) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | k2_partfun1(sK3,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f383,f47])).
% 1.65/0.61  fof(f383,plain,(
% 1.65/0.61    ( ! [X1] : (~v1_funct_2(X1,sK3,sK1) | ~v1_funct_1(X1) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X1),sK3) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | v1_xboole_0(sK3) | k2_partfun1(sK3,sK1,X1,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))) )),
% 1.65/0.61    inference(resolution,[],[f381,f48])).
% 1.65/0.61  fof(f381,plain,(
% 1.65/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~v1_funct_2(X0,X1,sK1) | ~v1_funct_1(X0) | k2_partfun1(k4_subset_1(sK0,sK2,X1),sK1,k1_tmap_1(sK0,sK1,sK2,X1,sK4,X0),X1) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | v1_xboole_0(X1) | k2_partfun1(X1,sK1,X0,k9_subset_1(sK0,sK2,X1)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,X1))) )),
% 1.65/0.61    inference(resolution,[],[f372,f46])).
% 1.65/0.61  fof(f372,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) != k7_relat_1(sK4,k9_subset_1(X0,sK2,X1))) )),
% 1.65/0.61    inference(forward_demodulation,[],[f371,f158])).
% 1.65/0.61  fof(f371,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f370,f69])).
% 1.65/0.61  fof(f370,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f369,f44])).
% 1.65/0.61  fof(f369,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f368,f45])).
% 1.65/0.61  fof(f368,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f367,f50])).
% 1.65/0.61  fof(f367,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2 | ~v1_funct_1(sK4) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f363,f52])).
% 1.65/0.61  fof(f363,plain,(
% 1.65/0.61    ( ! [X2,X0,X1] : (k2_partfun1(sK2,sK1,sK4,k9_subset_1(X0,sK2,X1)) != k2_partfun1(X1,sK1,X2,k9_subset_1(X0,sK2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(k4_subset_1(X0,sK2,X1),sK1,k1_tmap_1(X0,sK1,sK2,X1,sK4,X2),X1) = X2 | ~v1_funct_1(sK4) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(resolution,[],[f87,f51])).
% 1.65/0.61  fof(f87,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X4,X2,X1) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f86,f58])).
% 1.65/0.61  fof(f86,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f85,f59])).
% 1.65/0.61  fof(f85,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(subsumption_resolution,[],[f83,f57])).
% 1.65/0.61  fof(f83,plain,(
% 1.65/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(equality_resolution,[],[f61])).
% 1.65/0.61  fof(f61,plain,(
% 1.65/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.61    inference(cnf_transformation,[],[f40])).
% 1.65/0.61  fof(f163,plain,(
% 1.65/0.61    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.65/0.61    inference(subsumption_resolution,[],[f162,f106])).
% 1.65/0.61  fof(f162,plain,(
% 1.65/0.61    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.65/0.61    inference(backward_demodulation,[],[f160,f161])).
% 1.65/0.61  fof(f160,plain,(
% 1.65/0.61    k1_xboole_0 != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.65/0.61    inference(forward_demodulation,[],[f159,f100])).
% 1.65/0.61  fof(f159,plain,(
% 1.65/0.61    k7_relat_1(sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.65/0.61    inference(backward_demodulation,[],[f148,f158])).
% 1.65/0.61  fof(f148,plain,(
% 1.65/0.61    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) | sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.65/0.61    inference(backward_demodulation,[],[f56,f145])).
% 1.65/0.61  fof(f56,plain,(
% 1.65/0.61    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.65/0.61    inference(cnf_transformation,[],[f38])).
% 1.65/0.61  % SZS output end Proof for theBenchmark
% 1.65/0.61  % (7870)------------------------------
% 1.65/0.61  % (7870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.61  % (7870)Termination reason: Refutation
% 1.65/0.61  
% 1.65/0.61  % (7870)Memory used [KB]: 7291
% 1.65/0.61  % (7870)Time elapsed: 0.168 s
% 1.65/0.61  % (7870)------------------------------
% 1.65/0.61  % (7870)------------------------------
% 1.65/0.61  % (7864)Success in time 0.236 s
%------------------------------------------------------------------------------
