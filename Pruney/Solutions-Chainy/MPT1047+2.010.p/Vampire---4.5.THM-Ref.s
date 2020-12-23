%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:02 EST 2020

% Result     : Theorem 3.66s
% Output     : Refutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 930 expanded)
%              Number of leaves         :   33 ( 338 expanded)
%              Depth                    :   23
%              Number of atoms          : 1018 (6086 expanded)
%              Number of equality atoms :  173 (1272 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2771,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f171,f184,f303,f510,f638,f833,f976,f1138,f1543,f2276,f2394,f2698,f2770])).

fof(f2770,plain,
    ( ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_35
    | spl7_38
    | ~ spl7_47 ),
    inference(avatar_contradiction_clause,[],[f2769])).

fof(f2769,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_28
    | ~ spl7_35
    | spl7_38
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f2768,f832])).

fof(f832,plain,
    ( sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK3)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f830])).

fof(f830,plain,
    ( spl7_28
  <=> sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f2768,plain,
    ( sK3 != sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK3)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_35
    | spl7_38
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f1651,f2682])).

fof(f2682,plain,
    ( sK3 = sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_47 ),
    inference(backward_demodulation,[],[f2520,f2519])).

fof(f2519,plain,
    ( sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_47 ),
    inference(resolution,[],[f2274,f1606])).

fof(f1606,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_enumset1(sK3,sK3,sK3))
        | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X1) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_22
    | ~ spl7_35 ),
    inference(forward_demodulation,[],[f1605,f1542])).

fof(f1542,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f1540])).

fof(f1540,plain,
    ( spl7_35
  <=> k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f1605,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3))
        | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X1) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f1600,f100])).

fof(f100,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1600,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3))
        | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X1)
        | ~ v1_funct_1(sK3) )
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(resolution,[],[f721,f110])).

fof(f110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f721,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
        | ~ r2_hidden(X1,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0))
        | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1)
        | ~ v1_funct_1(X0) )
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f720,f85])).

fof(f85,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(sK6(X0,X1,X2,X7),X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_partfun1(sK6(X0,X1,X2,X7),X0)
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ( ( ! [X5] :
                    ( ~ r1_partfun1(X2,X5)
                    | ~ v1_partfun1(X5,X0)
                    | sK4(X0,X1,X2,X3) != X5
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    | ~ v1_funct_1(X5) )
                | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
              & ( ( r1_partfun1(X2,sK5(X0,X1,X2,X3))
                  & v1_partfun1(sK5(X0,X1,X2,X3),X0)
                  & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3)
                  & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(sK5(X0,X1,X2,X3)) )
                | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ( r1_partfun1(X2,sK6(X0,X1,X2,X7))
                    & v1_partfun1(sK6(X0,X1,X2,X7),X0)
                    & sK6(X0,X1,X2,X7) = X7
                    & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(sK6(X0,X1,X2,X7)) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X2,X5)
                | ~ v1_partfun1(X5,X0)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X2,X6)
                & v1_partfun1(X6,X0)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X2,X5)
              | ~ v1_partfun1(X5,X0)
              | sK4(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X2,X6)
              & v1_partfun1(X6,X0)
              & sK4(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X6) )
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X2,X6)
          & v1_partfun1(X6,X0)
          & sK4(X0,X1,X2,X3) = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X2,sK5(X0,X1,X2,X3))
        & v1_partfun1(sK5(X0,X1,X2,X3),X0)
        & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3)
        & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK5(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X2,X9)
          & v1_partfun1(X9,X0)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X2,sK6(X0,X1,X2,X7))
        & v1_partfun1(sK6(X0,X1,X2,X7),X0)
        & sK6(X0,X1,X2,X7) = X7
        & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK6(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X6] :
                      ( r1_partfun1(X2,X6)
                      & v1_partfun1(X6,X0)
                      & X4 = X6
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X6) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ? [X9] :
                      ( r1_partfun1(X2,X9)
                      & v1_partfun1(X9,X0)
                      & X7 = X9
                      & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X9) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X3)
                  | ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) ) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).

fof(f720,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1),sK0)
        | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1)
        | ~ r2_hidden(X1,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f717,f88])).

fof(f88,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(sK6(X0,X1,X2,X7)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_funct_1(sK6(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f717,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1))
        | ~ v1_partfun1(sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1),sK0)
        | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1)
        | ~ r2_hidden(X1,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl7_22 ),
    inference(resolution,[],[f509,f87])).

fof(f87,plain,(
    ! [X2,X0,X7,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f509,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
        | ~ v1_funct_1(X0)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0 )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl7_22
  <=> ! [X0] :
        ( ~ v1_partfun1(X0,sK0)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
        | sK3 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f2274,plain,
    ( r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f2273])).

fof(f2273,plain,
    ( spl7_47
  <=> r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f2520,plain,
    ( sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_47 ),
    inference(resolution,[],[f2274,f1248])).

fof(f1248,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_enumset1(sK3,sK3,sK3))
        | sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X0) = X0 )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f237,f1242])).

fof(f1242,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f100,f110,f228,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_partfun1(X0,X1,X2) = k1_enumset1(X2,X2,X2) ) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_partfun1(X0,X1,X2) = k1_tarski(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_partfun1(X2,X0)
          | k5_partfun1(X0,X1,X2) != k1_tarski(X2) )
        & ( k5_partfun1(X0,X1,X2) = k1_tarski(X2)
          | ~ v1_partfun1(X2,X0) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).

fof(f228,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl7_14
  <=> v1_partfun1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f237,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3))
        | sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X0) = X0 )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f142,f110])).

fof(f142,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ r2_hidden(X3,k5_partfun1(X4,X5,sK3))
        | sK6(X4,X5,sK3,X3) = X3 )
    | ~ spl7_2 ),
    inference(resolution,[],[f86,f100])).

fof(f86,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X7,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK6(X0,X1,X2,X7) = X7 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK6(X0,X1,X2,X7) = X7
      | ~ r2_hidden(X7,X3)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1651,plain,
    ( sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) != sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | spl7_38 ),
    inference(avatar_component_clause,[],[f1650])).

fof(f1650,plain,
    ( spl7_38
  <=> sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f2698,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_40
    | ~ spl7_47 ),
    inference(avatar_contradiction_clause,[],[f2697])).

fof(f2697,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_40
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f2696,f110])).

fof(f2696,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_40
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f2695,f2682])).

fof(f2695,plain,
    ( ~ m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_40
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f2694,f228])).

fof(f2694,plain,
    ( ~ v1_partfun1(sK3,sK0)
    | ~ m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_40
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f2693,f2682])).

fof(f2693,plain,
    ( ~ v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0)
    | ~ m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_40
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f2692,f183])).

fof(f183,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_11
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f2692,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0)
    | ~ m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_35
    | ~ spl7_40
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f2510,f2682])).

fof(f2510,plain,
    ( ~ r1_partfun1(sK2,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | ~ v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0)
    | ~ m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ spl7_1
    | ~ spl7_5
    | spl7_6
    | ~ spl7_40
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f2509,f95])).

fof(f95,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f2509,plain,
    ( ~ r1_partfun1(sK2,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | ~ v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0)
    | ~ m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl7_5
    | spl7_6
    | ~ spl7_40
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f2508,f115])).

fof(f115,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f2508,plain,
    ( ~ r1_partfun1(sK2,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | ~ v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0)
    | ~ m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ v1_funct_1(sK2)
    | spl7_6
    | ~ spl7_40
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f2507,f2274])).

fof(f2507,plain,
    ( ~ r1_partfun1(sK2,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | ~ v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0)
    | ~ m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ v1_funct_1(sK2)
    | spl7_6
    | ~ spl7_40 ),
    inference(subsumption_resolution,[],[f2492,f120])).

fof(f120,plain,
    ( k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) != k1_enumset1(sK3,sK3,sK3)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_6
  <=> k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = k1_enumset1(sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f2492,plain,
    ( ~ r1_partfun1(sK2,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | ~ v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0)
    | ~ m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = k1_enumset1(sK3,sK3,sK3)
    | ~ r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl7_40 ),
    inference(resolution,[],[f1694,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(sK4(X0,X1,X2,X3))
      | ~ r1_partfun1(X2,sK4(X0,X1,X2,X3))
      | ~ v1_partfun1(sK4(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_partfun1(X0,X1,X2) = X3
      | ~ r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( k5_partfun1(X0,X1,X2) = X3
      | ~ r1_partfun1(X2,X5)
      | ~ v1_partfun1(X5,X0)
      | sK4(X0,X1,X2,X3) != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1694,plain,
    ( v1_funct_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f1692])).

fof(f1692,plain,
    ( spl7_40
  <=> v1_funct_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f2394,plain,
    ( ~ spl7_1
    | ~ spl7_5
    | spl7_6
    | ~ spl7_16
    | ~ spl7_22
    | spl7_47 ),
    inference(avatar_contradiction_clause,[],[f2393])).

fof(f2393,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_5
    | spl7_6
    | ~ spl7_16
    | ~ spl7_22
    | spl7_47 ),
    inference(subsumption_resolution,[],[f2371,f302])).

fof(f302,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl7_16
  <=> r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f2371,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | ~ spl7_1
    | ~ spl7_5
    | spl7_6
    | ~ spl7_22
    | spl7_47 ),
    inference(backward_demodulation,[],[f2275,f2368])).

fof(f2368,plain,
    ( sK3 = sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))
    | ~ spl7_1
    | ~ spl7_5
    | spl7_6
    | ~ spl7_22
    | spl7_47 ),
    inference(backward_demodulation,[],[f2290,f2282])).

fof(f2282,plain,
    ( sK3 = sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))
    | ~ spl7_1
    | ~ spl7_5
    | spl7_6
    | ~ spl7_22
    | spl7_47 ),
    inference(unit_resulting_resolution,[],[f120,f2275,f821])).

fof(f821,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0)
        | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0
        | sK3 = sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f820,f285])).

fof(f285,plain,
    ( ! [X0] :
        ( v1_partfun1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),sK0)
        | r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0)
        | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0 )
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(resolution,[],[f172,f115])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r2_hidden(sK4(X0,X1,sK2,X2),X2)
        | v1_partfun1(sK5(X0,X1,sK2,X2),X0)
        | k5_partfun1(X0,X1,sK2) = X2 )
    | ~ spl7_1 ),
    inference(resolution,[],[f64,f95])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_partfun1(sK5(X0,X1,X2,X3),X0)
      | r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f820,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0)
        | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0
        | ~ v1_partfun1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),sK0)
        | sK3 = sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f814,f259])).

fof(f259,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0)
        | v1_funct_1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0))
        | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0 )
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(resolution,[],[f163,f115])).

fof(f163,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r2_hidden(sK4(X0,X1,sK2,X2),X2)
        | v1_funct_1(sK5(X0,X1,sK2,X2))
        | k5_partfun1(X0,X1,sK2) = X2 )
    | ~ spl7_1 ),
    inference(resolution,[],[f61,f95])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_funct_1(sK5(X0,X1,X2,X3))
      | r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f814,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0)
        | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0
        | ~ v1_funct_1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0))
        | ~ v1_partfun1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),sK0)
        | sK3 = sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0) )
    | ~ spl7_1
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(resolution,[],[f403,f509])).

fof(f403,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
        | r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0)
        | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0 )
    | ~ spl7_1
    | ~ spl7_5 ),
    inference(resolution,[],[f178,f115])).

fof(f178,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r2_hidden(sK4(X0,X1,sK2,X2),X2)
        | m1_subset_1(sK5(X0,X1,sK2,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k5_partfun1(X0,X1,sK2) = X2 )
    | ~ spl7_1 ),
    inference(resolution,[],[f62,f95])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2290,plain,
    ( sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) = sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))
    | ~ spl7_1
    | ~ spl7_5
    | spl7_6
    | spl7_47 ),
    inference(unit_resulting_resolution,[],[f115,f120,f2275,f185])).

fof(f185,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r2_hidden(sK4(X0,X1,sK2,X2),X2)
        | sK5(X0,X1,sK2,X2) = sK4(X0,X1,sK2,X2)
        | k5_partfun1(X0,X1,sK2) = X2 )
    | ~ spl7_1 ),
    inference(resolution,[],[f63,f95])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3)
      | r2_hidden(sK4(X0,X1,X2,X3),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_partfun1(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2275,plain,
    ( ~ r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | spl7_47 ),
    inference(avatar_component_clause,[],[f2273])).

fof(f2276,plain,
    ( ~ spl7_47
    | spl7_40
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f1663,f1650,f226,f108,f98,f1692,f2273])).

fof(f1663,plain,
    ( v1_funct_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | ~ r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_38 ),
    inference(superposition,[],[f1245,f1652])).

fof(f1652,plain,
    ( sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f1650])).

fof(f1245,plain,
    ( ! [X0] :
        ( v1_funct_1(sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X0))
        | ~ r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f210,f1242])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3))
        | v1_funct_1(sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X0)) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f136,f110])).

fof(f136,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ r2_hidden(X3,k5_partfun1(X4,X5,sK3))
        | v1_funct_1(sK6(X4,X5,sK3,X3)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f88,f100])).

fof(f1543,plain,
    ( spl7_35
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f1242,f226,f108,f98,f1540])).

fof(f1138,plain,
    ( ~ spl7_15
    | spl7_31 ),
    inference(avatar_contradiction_clause,[],[f1137])).

fof(f1137,plain,
    ( $false
    | ~ spl7_15
    | spl7_31 ),
    inference(subsumption_resolution,[],[f1092,f992])).

fof(f992,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl7_15 ),
    inference(superposition,[],[f991,f991])).

fof(f991,plain,
    ( ! [X6] : k1_xboole_0 = X6
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f983,f79])).

fof(f79,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f983,plain,
    ( ! [X6] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X6)
        | k1_xboole_0 = X6 )
    | ~ spl7_15 ),
    inference(superposition,[],[f74,f232])).

fof(f232,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl7_15
  <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_enumset1(X1,X1,X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f45,f68])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f1092,plain,
    ( k1_enumset1(sK3,sK3,sK3) != k5_partfun1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_15
    | spl7_31 ),
    inference(superposition,[],[f975,f991])).

fof(f975,plain,
    ( k1_enumset1(sK3,sK3,sK3) != k5_partfun1(sK0,k1_xboole_0,sK2)
    | spl7_31 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl7_31
  <=> k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f976,plain,
    ( ~ spl7_31
    | spl7_6
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f308,f230,f118,f973])).

fof(f308,plain,
    ( k1_enumset1(sK3,sK3,sK3) != k5_partfun1(sK0,k1_xboole_0,sK2)
    | spl7_6
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f120,f232])).

fof(f833,plain,
    ( spl7_28
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f711,f300,f226,f108,f98,f830])).

fof(f711,plain,
    ( sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK3)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f302,f652])).

fof(f652,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_enumset1(sK3,sK3,sK3))
        | sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X0) = X0 )
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f237,f648])).

fof(f648,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f100,f110,f228,f76])).

fof(f638,plain,
    ( spl7_14
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_15 ),
    inference(avatar_split_clause,[],[f444,f230,f108,f103,f98,f226])).

fof(f103,plain,
    ( spl7_3
  <=> v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f444,plain,
    ( v1_partfun1(sK3,sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f100,f105,f110,f231,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f231,plain,
    ( k1_xboole_0 != k1_enumset1(sK1,sK1,sK1)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f230])).

fof(f105,plain,
    ( v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f510,plain,
    ( spl7_22
    | ~ spl7_14
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f304,f108,f98,f226,f508])).

fof(f304,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK3,sK0)
        | ~ v1_partfun1(X0,sK0)
        | sK3 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f271,f246])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
        | r1_partfun1(X0,sK3)
        | ~ v1_funct_1(X0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f162,f110])).

fof(f162,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,k1_enumset1(X4,X4,X4))))
        | r1_partfun1(X5,sK3)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,k1_enumset1(X4,X4,X4))))
        | ~ v1_funct_1(X5) )
    | ~ spl7_2 ),
    inference(resolution,[],[f77,f100])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1))))
      | r1_partfun1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f67,f68,f68])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_1(X3) )
         => r1_partfun1(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).

fof(f271,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK3,sK0)
        | ~ v1_partfun1(X0,sK0)
        | ~ r1_partfun1(X0,sK3)
        | sK3 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))
        | ~ v1_funct_1(X0) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(resolution,[],[f166,f110])).

fof(f166,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_partfun1(sK3,X4)
        | ~ v1_partfun1(X3,X4)
        | ~ r1_partfun1(X3,sK3)
        | sK3 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3) )
    | ~ spl7_2 ),
    inference(resolution,[],[f54,f100])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f303,plain,
    ( spl7_16
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f258,f226,f168,f108,f98,f300])).

fof(f168,plain,
    ( spl7_10
  <=> r1_partfun1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f258,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f249,f253])).

fof(f253,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f100,f110,f228,f76])).

fof(f249,plain,
    ( r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3))
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f100,f100,f170,f110,f110,f228,f83])).

fof(f83,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ v1_funct_1(X8)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(X8,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f170,plain,
    ( r1_partfun1(sK3,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f168])).

fof(f184,plain,
    ( spl7_11
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f158,f113,f108,f98,f93,f181])).

fof(f158,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f95,f100,f115,f110,f77])).

fof(f171,plain,
    ( spl7_10
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f157,f108,f98,f168])).

fof(f157,plain,
    ( r1_partfun1(sK3,sK3)
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f100,f100,f110,f110,f77])).

fof(f121,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f69,f118])).

fof(f69,plain,(
    k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) != k1_enumset1(sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f42,f68,f68])).

fof(f42,plain,(
    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_2(sK3,sK0,k1_tarski(sK1))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
          & v1_funct_2(X3,sK0,k1_tarski(sK1))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        & v1_funct_2(X3,sK0,k1_tarski(sK1))
        & v1_funct_1(X3) )
   => ( k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
      & v1_funct_2(sK3,sK0,k1_tarski(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).

fof(f116,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f72,f113])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f38,f68])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f111,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f70,f108])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f71,f103])).

fof(f71,plain,(
    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f40,f68])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f39,f98])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f37,f93])).

fof(f37,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:57:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (4211)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (4203)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4219)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (4205)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (4220)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (4204)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (4198)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (4197)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (4198)Refutation not found, incomplete strategy% (4198)------------------------------
% 0.21/0.54  % (4198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4198)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4198)Memory used [KB]: 1663
% 0.21/0.54  % (4198)Time elapsed: 0.121 s
% 0.21/0.54  % (4198)------------------------------
% 0.21/0.54  % (4198)------------------------------
% 0.21/0.54  % (4199)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (4221)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (4218)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (4212)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (4213)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (4208)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (4217)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (4202)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (4200)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (4215)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (4209)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (4213)Refutation not found, incomplete strategy% (4213)------------------------------
% 0.21/0.55  % (4213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4213)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4213)Memory used [KB]: 10746
% 0.21/0.55  % (4213)Time elapsed: 0.131 s
% 0.21/0.55  % (4213)------------------------------
% 0.21/0.55  % (4213)------------------------------
% 0.21/0.55  % (4210)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (4222)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (4226)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (4206)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (4216)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (4226)Refutation not found, incomplete strategy% (4226)------------------------------
% 0.21/0.55  % (4226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4226)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4226)Memory used [KB]: 1663
% 0.21/0.55  % (4226)Time elapsed: 0.001 s
% 0.21/0.55  % (4226)------------------------------
% 0.21/0.55  % (4226)------------------------------
% 0.21/0.55  % (4223)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (4214)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (4201)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.56  % (4223)Refutation not found, incomplete strategy% (4223)------------------------------
% 0.21/0.56  % (4223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4223)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4223)Memory used [KB]: 6268
% 0.21/0.56  % (4223)Time elapsed: 0.149 s
% 0.21/0.56  % (4223)------------------------------
% 0.21/0.56  % (4223)------------------------------
% 0.21/0.56  % (4224)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (4224)Refutation not found, incomplete strategy% (4224)------------------------------
% 0.21/0.56  % (4224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (4224)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (4224)Memory used [KB]: 6140
% 0.21/0.56  % (4224)Time elapsed: 0.147 s
% 0.21/0.56  % (4224)------------------------------
% 0.21/0.56  % (4224)------------------------------
% 0.21/0.56  % (4207)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (4225)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.59  % (4201)Refutation not found, incomplete strategy% (4201)------------------------------
% 0.21/0.59  % (4201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (4201)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (4201)Memory used [KB]: 1918
% 0.21/0.59  % (4201)Time elapsed: 0.173 s
% 0.21/0.59  % (4201)------------------------------
% 0.21/0.59  % (4201)------------------------------
% 0.21/0.59  % (4215)Refutation not found, incomplete strategy% (4215)------------------------------
% 0.21/0.59  % (4215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (4215)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (4215)Memory used [KB]: 1791
% 0.21/0.60  % (4215)Time elapsed: 0.180 s
% 0.21/0.60  % (4215)------------------------------
% 0.21/0.60  % (4215)------------------------------
% 2.02/0.63  % (4209)Refutation not found, incomplete strategy% (4209)------------------------------
% 2.02/0.63  % (4209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.64  % (4209)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.64  
% 2.02/0.64  % (4209)Memory used [KB]: 11001
% 2.02/0.64  % (4209)Time elapsed: 0.220 s
% 2.02/0.64  % (4209)------------------------------
% 2.02/0.64  % (4209)------------------------------
% 2.02/0.68  % (4263)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.02/0.68  % (4259)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.02/0.69  % (4254)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.02/0.69  % (4264)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.02/0.69  % (4200)Refutation not found, incomplete strategy% (4200)------------------------------
% 2.02/0.69  % (4200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.69  % (4200)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.69  
% 2.02/0.69  % (4200)Memory used [KB]: 6268
% 2.02/0.69  % (4200)Time elapsed: 0.256 s
% 2.02/0.69  % (4200)------------------------------
% 2.02/0.69  % (4200)------------------------------
% 2.02/0.70  % (4199)Refutation not found, incomplete strategy% (4199)------------------------------
% 2.02/0.70  % (4199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.70  % (4199)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.70  
% 2.02/0.70  % (4199)Memory used [KB]: 6268
% 2.02/0.70  % (4199)Time elapsed: 0.283 s
% 2.02/0.70  % (4199)------------------------------
% 2.02/0.70  % (4199)------------------------------
% 2.02/0.70  % (4263)Refutation not found, incomplete strategy% (4263)------------------------------
% 2.02/0.70  % (4263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.70  % (4263)Termination reason: Refutation not found, incomplete strategy
% 2.02/0.70  
% 2.02/0.70  % (4263)Memory used [KB]: 10746
% 2.02/0.70  % (4263)Time elapsed: 0.109 s
% 2.02/0.70  % (4263)------------------------------
% 2.02/0.70  % (4263)------------------------------
% 2.63/0.71  % (4259)Refutation not found, incomplete strategy% (4259)------------------------------
% 2.63/0.71  % (4259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.63/0.71  % (4259)Termination reason: Refutation not found, incomplete strategy
% 2.63/0.71  
% 2.63/0.71  % (4259)Memory used [KB]: 6140
% 2.63/0.71  % (4259)Time elapsed: 0.122 s
% 2.63/0.71  % (4259)------------------------------
% 2.63/0.71  % (4259)------------------------------
% 2.63/0.71  % (4197)Refutation not found, incomplete strategy% (4197)------------------------------
% 2.63/0.71  % (4197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.63/0.71  % (4197)Termination reason: Refutation not found, incomplete strategy
% 2.63/0.71  
% 2.63/0.71  % (4197)Memory used [KB]: 1791
% 2.63/0.71  % (4197)Time elapsed: 0.247 s
% 2.63/0.71  % (4197)------------------------------
% 2.63/0.71  % (4197)------------------------------
% 2.63/0.72  % (4278)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.63/0.72  % (4256)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.63/0.72  % (4212)Refutation not found, incomplete strategy% (4212)------------------------------
% 2.63/0.72  % (4212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.63/0.72  % (4212)Termination reason: Refutation not found, incomplete strategy
% 2.63/0.72  
% 2.63/0.72  % (4212)Memory used [KB]: 6268
% 2.63/0.72  % (4212)Time elapsed: 0.290 s
% 2.63/0.72  % (4212)------------------------------
% 2.63/0.72  % (4212)------------------------------
% 2.63/0.72  % (4272)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.63/0.73  % (4278)Refutation not found, incomplete strategy% (4278)------------------------------
% 2.63/0.73  % (4278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.63/0.73  % (4278)Termination reason: Refutation not found, incomplete strategy
% 2.63/0.73  
% 2.63/0.73  % (4278)Memory used [KB]: 10746
% 2.63/0.73  % (4278)Time elapsed: 0.108 s
% 2.63/0.73  % (4278)------------------------------
% 2.63/0.73  % (4278)------------------------------
% 3.12/0.78  % (4295)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.12/0.80  % (4333)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.12/0.82  % (4342)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.12/0.83  % (4221)Time limit reached!
% 3.12/0.83  % (4221)------------------------------
% 3.12/0.83  % (4221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.83  % (4221)Termination reason: Time limit
% 3.12/0.83  
% 3.12/0.83  % (4221)Memory used [KB]: 12409
% 3.12/0.83  % (4221)Time elapsed: 0.413 s
% 3.12/0.83  % (4221)------------------------------
% 3.12/0.83  % (4221)------------------------------
% 3.12/0.83  % (4335)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.12/0.83  % (4345)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 3.12/0.83  % (4337)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.12/0.85  % (4359)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 3.66/0.87  % (4362)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.66/0.88  % (4217)Refutation found. Thanks to Tanya!
% 3.66/0.88  % SZS status Theorem for theBenchmark
% 3.66/0.88  % (4359)Refutation not found, incomplete strategy% (4359)------------------------------
% 3.66/0.88  % (4359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.88  % (4359)Termination reason: Refutation not found, incomplete strategy
% 3.66/0.88  
% 3.66/0.88  % (4359)Memory used [KB]: 10874
% 3.66/0.88  % (4359)Time elapsed: 0.137 s
% 3.66/0.88  % (4359)------------------------------
% 3.66/0.88  % (4359)------------------------------
% 3.66/0.88  % SZS output start Proof for theBenchmark
% 3.66/0.88  fof(f2771,plain,(
% 3.66/0.88    $false),
% 3.66/0.88    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f171,f184,f303,f510,f638,f833,f976,f1138,f1543,f2276,f2394,f2698,f2770])).
% 3.66/0.88  fof(f2770,plain,(
% 3.66/0.88    ~spl7_2 | ~spl7_4 | ~spl7_14 | ~spl7_22 | ~spl7_28 | ~spl7_35 | spl7_38 | ~spl7_47),
% 3.66/0.88    inference(avatar_contradiction_clause,[],[f2769])).
% 3.66/0.88  fof(f2769,plain,(
% 3.66/0.88    $false | (~spl7_2 | ~spl7_4 | ~spl7_14 | ~spl7_22 | ~spl7_28 | ~spl7_35 | spl7_38 | ~spl7_47)),
% 3.66/0.88    inference(subsumption_resolution,[],[f2768,f832])).
% 3.66/0.88  fof(f832,plain,(
% 3.66/0.88    sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK3) | ~spl7_28),
% 3.66/0.88    inference(avatar_component_clause,[],[f830])).
% 3.66/0.88  fof(f830,plain,(
% 3.66/0.88    spl7_28 <=> sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK3)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 3.66/0.88  fof(f2768,plain,(
% 3.66/0.88    sK3 != sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK3) | (~spl7_2 | ~spl7_4 | ~spl7_14 | ~spl7_22 | ~spl7_35 | spl7_38 | ~spl7_47)),
% 3.66/0.88    inference(forward_demodulation,[],[f1651,f2682])).
% 3.66/0.88  fof(f2682,plain,(
% 3.66/0.88    sK3 = sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) | (~spl7_2 | ~spl7_4 | ~spl7_14 | ~spl7_22 | ~spl7_35 | ~spl7_47)),
% 3.66/0.88    inference(backward_demodulation,[],[f2520,f2519])).
% 3.66/0.88  fof(f2519,plain,(
% 3.66/0.88    sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | (~spl7_2 | ~spl7_4 | ~spl7_22 | ~spl7_35 | ~spl7_47)),
% 3.66/0.88    inference(resolution,[],[f2274,f1606])).
% 3.66/0.88  fof(f1606,plain,(
% 3.66/0.88    ( ! [X1] : (~r2_hidden(X1,k1_enumset1(sK3,sK3,sK3)) | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X1)) ) | (~spl7_2 | ~spl7_4 | ~spl7_22 | ~spl7_35)),
% 3.66/0.88    inference(forward_demodulation,[],[f1605,f1542])).
% 3.66/0.88  fof(f1542,plain,(
% 3.66/0.88    k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) | ~spl7_35),
% 3.66/0.88    inference(avatar_component_clause,[],[f1540])).
% 3.66/0.88  fof(f1540,plain,(
% 3.66/0.88    spl7_35 <=> k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 3.66/0.88  fof(f1605,plain,(
% 3.66/0.88    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)) | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X1)) ) | (~spl7_2 | ~spl7_4 | ~spl7_22)),
% 3.66/0.88    inference(subsumption_resolution,[],[f1600,f100])).
% 3.66/0.88  fof(f100,plain,(
% 3.66/0.88    v1_funct_1(sK3) | ~spl7_2),
% 3.66/0.88    inference(avatar_component_clause,[],[f98])).
% 3.66/0.88  fof(f98,plain,(
% 3.66/0.88    spl7_2 <=> v1_funct_1(sK3)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 3.66/0.88  fof(f1600,plain,(
% 3.66/0.88    ( ! [X1] : (~r2_hidden(X1,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)) | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X1) | ~v1_funct_1(sK3)) ) | (~spl7_4 | ~spl7_22)),
% 3.66/0.88    inference(resolution,[],[f721,f110])).
% 3.66/0.88  fof(f110,plain,(
% 3.66/0.88    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~spl7_4),
% 3.66/0.88    inference(avatar_component_clause,[],[f108])).
% 3.66/0.88  fof(f108,plain,(
% 3.66/0.88    spl7_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 3.66/0.88  fof(f721,plain,(
% 3.66/0.88    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~r2_hidden(X1,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0)) | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1) | ~v1_funct_1(X0)) ) | ~spl7_22),
% 3.66/0.88    inference(subsumption_resolution,[],[f720,f85])).
% 3.66/0.88  fof(f85,plain,(
% 3.66/0.88    ( ! [X2,X0,X7,X1] : (~v1_funct_1(X2) | ~r2_hidden(X7,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK6(X0,X1,X2,X7),X0)) )),
% 3.66/0.88    inference(equality_resolution,[],[f58])).
% 3.66/0.88  fof(f58,plain,(
% 3.66/0.88    ( ! [X2,X0,X7,X3,X1] : (v1_partfun1(sK6(X0,X1,X2,X7),X0) | ~r2_hidden(X7,X3) | k5_partfun1(X0,X1,X2) != X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f36])).
% 3.66/0.88  fof(f36,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | sK4(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & ((r1_partfun1(X2,sK5(X0,X1,X2,X3)) & v1_partfun1(sK5(X0,X1,X2,X3),X0) & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK5(X0,X1,X2,X3))) | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8))) & ((r1_partfun1(X2,sK6(X0,X1,X2,X7)) & v1_partfun1(sK6(X0,X1,X2,X7),X0) & sK6(X0,X1,X2,X7) = X7 & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK6(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | k5_partfun1(X0,X1,X2) != X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.66/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).
% 3.66/0.88  fof(f33,plain,(
% 3.66/0.88    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | sK4(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & sK4(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 3.66/0.88    introduced(choice_axiom,[])).
% 3.66/0.88  fof(f34,plain,(
% 3.66/0.88    ! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & sK4(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) => (r1_partfun1(X2,sK5(X0,X1,X2,X3)) & v1_partfun1(sK5(X0,X1,X2,X3),X0) & sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3) & m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK5(X0,X1,X2,X3))))),
% 3.66/0.88    introduced(choice_axiom,[])).
% 3.66/0.88  fof(f35,plain,(
% 3.66/0.88    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X2,X9) & v1_partfun1(X9,X0) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X9)) => (r1_partfun1(X2,sK6(X0,X1,X2,X7)) & v1_partfun1(sK6(X0,X1,X2,X7),X0) & sK6(X0,X1,X2,X7) = X7 & m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK6(X0,X1,X2,X7))))),
% 3.66/0.88    introduced(choice_axiom,[])).
% 3.66/0.88  fof(f32,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X2,X6) & v1_partfun1(X6,X0) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X2,X9) & v1_partfun1(X9,X0) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | k5_partfun1(X0,X1,X2) != X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.66/0.88    inference(rectify,[],[f31])).
% 3.66/0.88  fof(f31,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | k5_partfun1(X0,X1,X2) != X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.66/0.88    inference(nnf_transformation,[],[f22])).
% 3.66/0.88  fof(f22,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.66/0.88    inference(flattening,[],[f21])).
% 3.66/0.88  fof(f21,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.66/0.88    inference(ennf_transformation,[],[f5])).
% 3.66/0.88  fof(f5,axiom,(
% 3.66/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 3.66/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_partfun1)).
% 3.66/0.88  fof(f720,plain,(
% 3.66/0.88    ( ! [X0,X1] : (~v1_partfun1(sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1),sK0) | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1) | ~r2_hidden(X1,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(X0)) ) | ~spl7_22),
% 3.66/0.88    inference(subsumption_resolution,[],[f717,f88])).
% 3.66/0.88  fof(f88,plain,(
% 3.66/0.88    ( ! [X2,X0,X7,X1] : (~v1_funct_1(X2) | ~r2_hidden(X7,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(sK6(X0,X1,X2,X7))) )),
% 3.66/0.88    inference(equality_resolution,[],[f55])).
% 3.66/0.88  fof(f55,plain,(
% 3.66/0.88    ( ! [X2,X0,X7,X3,X1] : (v1_funct_1(sK6(X0,X1,X2,X7)) | ~r2_hidden(X7,X3) | k5_partfun1(X0,X1,X2) != X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f36])).
% 3.66/0.88  fof(f717,plain,(
% 3.66/0.88    ( ! [X0,X1] : (~v1_funct_1(sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1)) | ~v1_partfun1(sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1),sK0) | sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),X0,X1) | ~r2_hidden(X1,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(X0)) ) | ~spl7_22),
% 3.66/0.88    inference(resolution,[],[f509,f87])).
% 3.66/0.88  fof(f87,plain,(
% 3.66/0.88    ( ! [X2,X0,X7,X1] : (m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X7,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(equality_resolution,[],[f56])).
% 3.66/0.88  fof(f56,plain,(
% 3.66/0.88    ( ! [X2,X0,X7,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X7,X3) | k5_partfun1(X0,X1,X2) != X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f36])).
% 3.66/0.88  fof(f509,plain,(
% 3.66/0.88    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(X0) | ~v1_partfun1(X0,sK0) | sK3 = X0) ) | ~spl7_22),
% 3.66/0.88    inference(avatar_component_clause,[],[f508])).
% 3.66/0.88  fof(f508,plain,(
% 3.66/0.88    spl7_22 <=> ! [X0] : (~v1_partfun1(X0,sK0) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | sK3 = X0)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 3.66/0.88  fof(f2274,plain,(
% 3.66/0.88    r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3)) | ~spl7_47),
% 3.66/0.88    inference(avatar_component_clause,[],[f2273])).
% 3.66/0.88  fof(f2273,plain,(
% 3.66/0.88    spl7_47 <=> r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 3.66/0.88  fof(f2520,plain,(
% 3.66/0.88    sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | (~spl7_2 | ~spl7_4 | ~spl7_14 | ~spl7_47)),
% 3.66/0.88    inference(resolution,[],[f2274,f1248])).
% 3.66/0.88  fof(f1248,plain,(
% 3.66/0.88    ( ! [X0] : (~r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) | sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X0) = X0) ) | (~spl7_2 | ~spl7_4 | ~spl7_14)),
% 3.66/0.88    inference(backward_demodulation,[],[f237,f1242])).
% 3.66/0.88  fof(f1242,plain,(
% 3.66/0.88    k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) | (~spl7_2 | ~spl7_4 | ~spl7_14)),
% 3.66/0.88    inference(unit_resulting_resolution,[],[f100,f110,f228,f76])).
% 3.66/0.88  fof(f76,plain,(
% 3.66/0.88    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,X2) = k1_enumset1(X2,X2,X2)) )),
% 3.66/0.88    inference(definition_unfolding,[],[f52,f68])).
% 3.66/0.88  fof(f68,plain,(
% 3.66/0.88    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.66/0.88    inference(definition_unfolding,[],[f43,f44])).
% 3.66/0.88  fof(f44,plain,(
% 3.66/0.88    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f2])).
% 3.66/0.88  fof(f2,axiom,(
% 3.66/0.88    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.66/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 3.66/0.88  fof(f43,plain,(
% 3.66/0.88    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f1])).
% 3.66/0.88  fof(f1,axiom,(
% 3.66/0.88    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.66/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 3.66/0.88  fof(f52,plain,(
% 3.66/0.88    ( ! [X2,X0,X1] : (k5_partfun1(X0,X1,X2) = k1_tarski(X2) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f30])).
% 3.66/0.88  fof(f30,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | k5_partfun1(X0,X1,X2) != k1_tarski(X2)) & (k5_partfun1(X0,X1,X2) = k1_tarski(X2) | ~v1_partfun1(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.66/0.88    inference(nnf_transformation,[],[f18])).
% 3.66/0.88  fof(f18,plain,(
% 3.66/0.88    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.66/0.88    inference(flattening,[],[f17])).
% 3.66/0.88  fof(f17,plain,(
% 3.66/0.88    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.66/0.88    inference(ennf_transformation,[],[f9])).
% 3.66/0.88  fof(f9,axiom,(
% 3.66/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2)))),
% 3.66/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_partfun1)).
% 3.66/0.88  fof(f228,plain,(
% 3.66/0.88    v1_partfun1(sK3,sK0) | ~spl7_14),
% 3.66/0.88    inference(avatar_component_clause,[],[f226])).
% 3.66/0.88  fof(f226,plain,(
% 3.66/0.88    spl7_14 <=> v1_partfun1(sK3,sK0)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 3.66/0.88  fof(f237,plain,(
% 3.66/0.88    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)) | sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X0) = X0) ) | (~spl7_2 | ~spl7_4)),
% 3.66/0.88    inference(resolution,[],[f142,f110])).
% 3.66/0.88  fof(f142,plain,(
% 3.66/0.88    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~r2_hidden(X3,k5_partfun1(X4,X5,sK3)) | sK6(X4,X5,sK3,X3) = X3) ) | ~spl7_2),
% 3.66/0.88    inference(resolution,[],[f86,f100])).
% 3.66/0.88  fof(f86,plain,(
% 3.66/0.88    ( ! [X2,X0,X7,X1] : (~v1_funct_1(X2) | ~r2_hidden(X7,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK6(X0,X1,X2,X7) = X7) )),
% 3.66/0.88    inference(equality_resolution,[],[f57])).
% 3.66/0.88  fof(f57,plain,(
% 3.66/0.88    ( ! [X2,X0,X7,X3,X1] : (sK6(X0,X1,X2,X7) = X7 | ~r2_hidden(X7,X3) | k5_partfun1(X0,X1,X2) != X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f36])).
% 3.66/0.88  fof(f1651,plain,(
% 3.66/0.88    sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) != sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | spl7_38),
% 3.66/0.88    inference(avatar_component_clause,[],[f1650])).
% 3.66/0.88  fof(f1650,plain,(
% 3.66/0.88    spl7_38 <=> sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 3.66/0.88  fof(f2698,plain,(
% 3.66/0.88    ~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11 | ~spl7_14 | ~spl7_22 | ~spl7_35 | ~spl7_40 | ~spl7_47),
% 3.66/0.88    inference(avatar_contradiction_clause,[],[f2697])).
% 3.66/0.88  fof(f2697,plain,(
% 3.66/0.88    $false | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11 | ~spl7_14 | ~spl7_22 | ~spl7_35 | ~spl7_40 | ~spl7_47)),
% 3.66/0.88    inference(subsumption_resolution,[],[f2696,f110])).
% 3.66/0.88  fof(f2696,plain,(
% 3.66/0.88    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11 | ~spl7_14 | ~spl7_22 | ~spl7_35 | ~spl7_40 | ~spl7_47)),
% 3.66/0.88    inference(forward_demodulation,[],[f2695,f2682])).
% 3.66/0.88  fof(f2695,plain,(
% 3.66/0.88    ~m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11 | ~spl7_14 | ~spl7_22 | ~spl7_35 | ~spl7_40 | ~spl7_47)),
% 3.66/0.88    inference(subsumption_resolution,[],[f2694,f228])).
% 3.66/0.88  fof(f2694,plain,(
% 3.66/0.88    ~v1_partfun1(sK3,sK0) | ~m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11 | ~spl7_14 | ~spl7_22 | ~spl7_35 | ~spl7_40 | ~spl7_47)),
% 3.66/0.88    inference(forward_demodulation,[],[f2693,f2682])).
% 3.66/0.88  fof(f2693,plain,(
% 3.66/0.88    ~v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0) | ~m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11 | ~spl7_14 | ~spl7_22 | ~spl7_35 | ~spl7_40 | ~spl7_47)),
% 3.66/0.88    inference(subsumption_resolution,[],[f2692,f183])).
% 3.66/0.88  fof(f183,plain,(
% 3.66/0.88    r1_partfun1(sK2,sK3) | ~spl7_11),
% 3.66/0.88    inference(avatar_component_clause,[],[f181])).
% 3.66/0.88  fof(f181,plain,(
% 3.66/0.88    spl7_11 <=> r1_partfun1(sK2,sK3)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 3.66/0.88  fof(f2692,plain,(
% 3.66/0.88    ~r1_partfun1(sK2,sK3) | ~v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0) | ~m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_14 | ~spl7_22 | ~spl7_35 | ~spl7_40 | ~spl7_47)),
% 3.66/0.88    inference(forward_demodulation,[],[f2510,f2682])).
% 3.66/0.88  fof(f2510,plain,(
% 3.66/0.88    ~r1_partfun1(sK2,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | ~v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0) | ~m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | (~spl7_1 | ~spl7_5 | spl7_6 | ~spl7_40 | ~spl7_47)),
% 3.66/0.88    inference(subsumption_resolution,[],[f2509,f95])).
% 3.66/0.88  fof(f95,plain,(
% 3.66/0.88    v1_funct_1(sK2) | ~spl7_1),
% 3.66/0.88    inference(avatar_component_clause,[],[f93])).
% 3.66/0.88  fof(f93,plain,(
% 3.66/0.88    spl7_1 <=> v1_funct_1(sK2)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 3.66/0.88  fof(f2509,plain,(
% 3.66/0.88    ~r1_partfun1(sK2,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | ~v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0) | ~m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(sK2) | (~spl7_5 | spl7_6 | ~spl7_40 | ~spl7_47)),
% 3.66/0.88    inference(subsumption_resolution,[],[f2508,f115])).
% 3.66/0.88  fof(f115,plain,(
% 3.66/0.88    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~spl7_5),
% 3.66/0.88    inference(avatar_component_clause,[],[f113])).
% 3.66/0.88  fof(f113,plain,(
% 3.66/0.88    spl7_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 3.66/0.88  fof(f2508,plain,(
% 3.66/0.88    ~r1_partfun1(sK2,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | ~v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0) | ~m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(sK2) | (spl7_6 | ~spl7_40 | ~spl7_47)),
% 3.66/0.88    inference(subsumption_resolution,[],[f2507,f2274])).
% 3.66/0.88  fof(f2507,plain,(
% 3.66/0.88    ~r1_partfun1(sK2,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | ~v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0) | ~m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(sK2) | (spl7_6 | ~spl7_40)),
% 3.66/0.88    inference(subsumption_resolution,[],[f2492,f120])).
% 3.66/0.88  fof(f120,plain,(
% 3.66/0.88    k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) != k1_enumset1(sK3,sK3,sK3) | spl7_6),
% 3.66/0.88    inference(avatar_component_clause,[],[f118])).
% 3.66/0.88  fof(f118,plain,(
% 3.66/0.88    spl7_6 <=> k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = k1_enumset1(sK3,sK3,sK3)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 3.66/0.88  fof(f2492,plain,(
% 3.66/0.88    ~r1_partfun1(sK2,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | ~v1_partfun1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),sK0) | ~m1_subset_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = k1_enumset1(sK3,sK3,sK3) | ~r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(sK2) | ~spl7_40),
% 3.66/0.88    inference(resolution,[],[f1694,f81])).
% 3.66/0.88  fof(f81,plain,(
% 3.66/0.88    ( ! [X2,X0,X3,X1] : (~v1_funct_1(sK4(X0,X1,X2,X3)) | ~r1_partfun1(X2,sK4(X0,X1,X2,X3)) | ~v1_partfun1(sK4(X0,X1,X2,X3),X0) | ~m1_subset_1(sK4(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,X2) = X3 | ~r2_hidden(sK4(X0,X1,X2,X3),X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(equality_resolution,[],[f66])).
% 3.66/0.88  fof(f66,plain,(
% 3.66/0.88    ( ! [X2,X0,X5,X3,X1] : (k5_partfun1(X0,X1,X2) = X3 | ~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | sK4(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~r2_hidden(sK4(X0,X1,X2,X3),X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f36])).
% 3.66/0.88  fof(f1694,plain,(
% 3.66/0.88    v1_funct_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | ~spl7_40),
% 3.66/0.88    inference(avatar_component_clause,[],[f1692])).
% 3.66/0.88  fof(f1692,plain,(
% 3.66/0.88    spl7_40 <=> v1_funct_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)))),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 3.66/0.88  fof(f2394,plain,(
% 3.66/0.88    ~spl7_1 | ~spl7_5 | spl7_6 | ~spl7_16 | ~spl7_22 | spl7_47),
% 3.66/0.88    inference(avatar_contradiction_clause,[],[f2393])).
% 3.66/0.88  fof(f2393,plain,(
% 3.66/0.88    $false | (~spl7_1 | ~spl7_5 | spl7_6 | ~spl7_16 | ~spl7_22 | spl7_47)),
% 3.66/0.88    inference(subsumption_resolution,[],[f2371,f302])).
% 3.66/0.88  fof(f302,plain,(
% 3.66/0.88    r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | ~spl7_16),
% 3.66/0.88    inference(avatar_component_clause,[],[f300])).
% 3.66/0.88  fof(f300,plain,(
% 3.66/0.88    spl7_16 <=> r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 3.66/0.88  fof(f2371,plain,(
% 3.66/0.88    ~r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | (~spl7_1 | ~spl7_5 | spl7_6 | ~spl7_22 | spl7_47)),
% 3.66/0.88    inference(backward_demodulation,[],[f2275,f2368])).
% 3.66/0.88  fof(f2368,plain,(
% 3.66/0.88    sK3 = sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) | (~spl7_1 | ~spl7_5 | spl7_6 | ~spl7_22 | spl7_47)),
% 3.66/0.88    inference(backward_demodulation,[],[f2290,f2282])).
% 3.66/0.88  fof(f2282,plain,(
% 3.66/0.88    sK3 = sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) | (~spl7_1 | ~spl7_5 | spl7_6 | ~spl7_22 | spl7_47)),
% 3.66/0.88    inference(unit_resulting_resolution,[],[f120,f2275,f821])).
% 3.66/0.88  fof(f821,plain,(
% 3.66/0.88    ( ! [X0] : (r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0) | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0 | sK3 = sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0)) ) | (~spl7_1 | ~spl7_5 | ~spl7_22)),
% 3.66/0.88    inference(subsumption_resolution,[],[f820,f285])).
% 3.66/0.88  fof(f285,plain,(
% 3.66/0.88    ( ! [X0] : (v1_partfun1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),sK0) | r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0) | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0) ) | (~spl7_1 | ~spl7_5)),
% 3.66/0.88    inference(resolution,[],[f172,f115])).
% 3.66/0.88  fof(f172,plain,(
% 3.66/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,sK2,X2),X2) | v1_partfun1(sK5(X0,X1,sK2,X2),X0) | k5_partfun1(X0,X1,sK2) = X2) ) | ~spl7_1),
% 3.66/0.88    inference(resolution,[],[f64,f95])).
% 3.66/0.88  fof(f64,plain,(
% 3.66/0.88    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_partfun1(sK5(X0,X1,X2,X3),X0) | r2_hidden(sK4(X0,X1,X2,X3),X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,X2) = X3) )),
% 3.66/0.88    inference(cnf_transformation,[],[f36])).
% 3.66/0.88  fof(f820,plain,(
% 3.66/0.88    ( ! [X0] : (r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0) | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0 | ~v1_partfun1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),sK0) | sK3 = sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0)) ) | (~spl7_1 | ~spl7_5 | ~spl7_22)),
% 3.66/0.88    inference(subsumption_resolution,[],[f814,f259])).
% 3.66/0.88  fof(f259,plain,(
% 3.66/0.88    ( ! [X0] : (r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0) | v1_funct_1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0)) | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0) ) | (~spl7_1 | ~spl7_5)),
% 3.66/0.88    inference(resolution,[],[f163,f115])).
% 3.66/0.88  fof(f163,plain,(
% 3.66/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,sK2,X2),X2) | v1_funct_1(sK5(X0,X1,sK2,X2)) | k5_partfun1(X0,X1,sK2) = X2) ) | ~spl7_1),
% 3.66/0.88    inference(resolution,[],[f61,f95])).
% 3.66/0.88  fof(f61,plain,(
% 3.66/0.88    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_funct_1(sK5(X0,X1,X2,X3)) | r2_hidden(sK4(X0,X1,X2,X3),X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,X2) = X3) )),
% 3.66/0.88    inference(cnf_transformation,[],[f36])).
% 3.66/0.88  fof(f814,plain,(
% 3.66/0.88    ( ! [X0] : (r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0) | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0 | ~v1_funct_1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0)) | ~v1_partfun1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),sK0) | sK3 = sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0)) ) | (~spl7_1 | ~spl7_5 | ~spl7_22)),
% 3.66/0.88    inference(resolution,[],[f403,f509])).
% 3.66/0.88  fof(f403,plain,(
% 3.66/0.88    ( ! [X0] : (m1_subset_1(sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,X0),X0) | k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) = X0) ) | (~spl7_1 | ~spl7_5)),
% 3.66/0.88    inference(resolution,[],[f178,f115])).
% 3.66/0.88  fof(f178,plain,(
% 3.66/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,sK2,X2),X2) | m1_subset_1(sK5(X0,X1,sK2,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,sK2) = X2) ) | ~spl7_1),
% 3.66/0.88    inference(resolution,[],[f62,f95])).
% 3.66/0.88  fof(f62,plain,(
% 3.66/0.88    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | m1_subset_1(sK5(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,X2,X3),X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,X2) = X3) )),
% 3.66/0.88    inference(cnf_transformation,[],[f36])).
% 3.66/0.88  fof(f2290,plain,(
% 3.66/0.88    sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) = sK5(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) | (~spl7_1 | ~spl7_5 | spl7_6 | spl7_47)),
% 3.66/0.88    inference(unit_resulting_resolution,[],[f115,f120,f2275,f185])).
% 3.66/0.88  fof(f185,plain,(
% 3.66/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,sK2,X2),X2) | sK5(X0,X1,sK2,X2) = sK4(X0,X1,sK2,X2) | k5_partfun1(X0,X1,sK2) = X2) ) | ~spl7_1),
% 3.66/0.88    inference(resolution,[],[f63,f95])).
% 3.66/0.88  fof(f63,plain,(
% 3.66/0.88    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | sK4(X0,X1,X2,X3) = sK5(X0,X1,X2,X3) | r2_hidden(sK4(X0,X1,X2,X3),X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_partfun1(X0,X1,X2) = X3) )),
% 3.66/0.88    inference(cnf_transformation,[],[f36])).
% 3.66/0.88  fof(f2275,plain,(
% 3.66/0.88    ~r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3)) | spl7_47),
% 3.66/0.88    inference(avatar_component_clause,[],[f2273])).
% 3.66/0.88  fof(f2276,plain,(
% 3.66/0.88    ~spl7_47 | spl7_40 | ~spl7_2 | ~spl7_4 | ~spl7_14 | ~spl7_38),
% 3.66/0.88    inference(avatar_split_clause,[],[f1663,f1650,f226,f108,f98,f1692,f2273])).
% 3.66/0.88  fof(f1663,plain,(
% 3.66/0.88    v1_funct_1(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | ~r2_hidden(sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3)) | (~spl7_2 | ~spl7_4 | ~spl7_14 | ~spl7_38)),
% 3.66/0.88    inference(superposition,[],[f1245,f1652])).
% 3.66/0.88  fof(f1652,plain,(
% 3.66/0.88    sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3)) = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK4(sK0,k1_enumset1(sK1,sK1,sK1),sK2,k1_enumset1(sK3,sK3,sK3))) | ~spl7_38),
% 3.66/0.88    inference(avatar_component_clause,[],[f1650])).
% 3.66/0.88  fof(f1245,plain,(
% 3.66/0.88    ( ! [X0] : (v1_funct_1(sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X0)) | ~r2_hidden(X0,k1_enumset1(sK3,sK3,sK3))) ) | (~spl7_2 | ~spl7_4 | ~spl7_14)),
% 3.66/0.88    inference(backward_demodulation,[],[f210,f1242])).
% 3.66/0.88  fof(f210,plain,(
% 3.66/0.88    ( ! [X0] : (~r2_hidden(X0,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)) | v1_funct_1(sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X0))) ) | (~spl7_2 | ~spl7_4)),
% 3.66/0.88    inference(resolution,[],[f136,f110])).
% 3.66/0.88  fof(f136,plain,(
% 3.66/0.88    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~r2_hidden(X3,k5_partfun1(X4,X5,sK3)) | v1_funct_1(sK6(X4,X5,sK3,X3))) ) | ~spl7_2),
% 3.66/0.88    inference(resolution,[],[f88,f100])).
% 3.66/0.88  fof(f1543,plain,(
% 3.66/0.88    spl7_35 | ~spl7_2 | ~spl7_4 | ~spl7_14),
% 3.66/0.88    inference(avatar_split_clause,[],[f1242,f226,f108,f98,f1540])).
% 3.66/0.88  fof(f1138,plain,(
% 3.66/0.88    ~spl7_15 | spl7_31),
% 3.66/0.88    inference(avatar_contradiction_clause,[],[f1137])).
% 3.66/0.88  fof(f1137,plain,(
% 3.66/0.88    $false | (~spl7_15 | spl7_31)),
% 3.66/0.88    inference(subsumption_resolution,[],[f1092,f992])).
% 3.66/0.88  fof(f992,plain,(
% 3.66/0.88    ( ! [X0,X1] : (X0 = X1) ) | ~spl7_15),
% 3.66/0.88    inference(superposition,[],[f991,f991])).
% 3.66/0.88  fof(f991,plain,(
% 3.66/0.88    ( ! [X6] : (k1_xboole_0 = X6) ) | ~spl7_15),
% 3.66/0.88    inference(subsumption_resolution,[],[f983,f79])).
% 3.66/0.88  fof(f79,plain,(
% 3.66/0.88    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.66/0.88    inference(equality_resolution,[],[f48])).
% 3.66/0.88  fof(f48,plain,(
% 3.66/0.88    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.66/0.88    inference(cnf_transformation,[],[f29])).
% 3.66/0.88  fof(f29,plain,(
% 3.66/0.88    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.66/0.88    inference(flattening,[],[f28])).
% 3.66/0.88  fof(f28,plain,(
% 3.66/0.88    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.66/0.88    inference(nnf_transformation,[],[f3])).
% 3.66/0.88  fof(f3,axiom,(
% 3.66/0.88    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.66/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.66/0.88  fof(f983,plain,(
% 3.66/0.88    ( ! [X6] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X6) | k1_xboole_0 = X6) ) | ~spl7_15),
% 3.66/0.88    inference(superposition,[],[f74,f232])).
% 3.66/0.88  fof(f232,plain,(
% 3.66/0.88    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | ~spl7_15),
% 3.66/0.88    inference(avatar_component_clause,[],[f230])).
% 3.66/0.88  fof(f230,plain,(
% 3.66/0.88    spl7_15 <=> k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 3.66/0.88  fof(f74,plain,(
% 3.66/0.88    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_enumset1(X1,X1,X1),X0) | k1_xboole_0 = X0) )),
% 3.66/0.88    inference(definition_unfolding,[],[f45,f68])).
% 3.66/0.88  fof(f45,plain,(
% 3.66/0.88    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) | k1_xboole_0 = X0) )),
% 3.66/0.88    inference(cnf_transformation,[],[f14])).
% 3.66/0.88  fof(f14,plain,(
% 3.66/0.88    ! [X0,X1] : ((k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)) | k1_xboole_0 = X0)),
% 3.66/0.88    inference(ennf_transformation,[],[f4])).
% 3.66/0.88  fof(f4,axiom,(
% 3.66/0.88    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 3.66/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 3.66/0.88  fof(f1092,plain,(
% 3.66/0.88    k1_enumset1(sK3,sK3,sK3) != k5_partfun1(sK0,k1_xboole_0,k1_xboole_0) | (~spl7_15 | spl7_31)),
% 3.66/0.88    inference(superposition,[],[f975,f991])).
% 3.66/0.88  fof(f975,plain,(
% 3.66/0.88    k1_enumset1(sK3,sK3,sK3) != k5_partfun1(sK0,k1_xboole_0,sK2) | spl7_31),
% 3.66/0.88    inference(avatar_component_clause,[],[f973])).
% 3.66/0.88  fof(f973,plain,(
% 3.66/0.88    spl7_31 <=> k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_xboole_0,sK2)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 3.66/0.88  fof(f976,plain,(
% 3.66/0.88    ~spl7_31 | spl7_6 | ~spl7_15),
% 3.66/0.88    inference(avatar_split_clause,[],[f308,f230,f118,f973])).
% 3.66/0.88  fof(f308,plain,(
% 3.66/0.88    k1_enumset1(sK3,sK3,sK3) != k5_partfun1(sK0,k1_xboole_0,sK2) | (spl7_6 | ~spl7_15)),
% 3.66/0.88    inference(backward_demodulation,[],[f120,f232])).
% 3.66/0.88  fof(f833,plain,(
% 3.66/0.88    spl7_28 | ~spl7_2 | ~spl7_4 | ~spl7_14 | ~spl7_16),
% 3.66/0.88    inference(avatar_split_clause,[],[f711,f300,f226,f108,f98,f830])).
% 3.66/0.88  fof(f711,plain,(
% 3.66/0.88    sK3 = sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,sK3) | (~spl7_2 | ~spl7_4 | ~spl7_14 | ~spl7_16)),
% 3.66/0.88    inference(unit_resulting_resolution,[],[f302,f652])).
% 3.66/0.88  fof(f652,plain,(
% 3.66/0.88    ( ! [X0] : (~r2_hidden(X0,k1_enumset1(sK3,sK3,sK3)) | sK6(sK0,k1_enumset1(sK1,sK1,sK1),sK3,X0) = X0) ) | (~spl7_2 | ~spl7_4 | ~spl7_14)),
% 3.66/0.88    inference(backward_demodulation,[],[f237,f648])).
% 3.66/0.88  fof(f648,plain,(
% 3.66/0.88    k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) | (~spl7_2 | ~spl7_4 | ~spl7_14)),
% 3.66/0.88    inference(unit_resulting_resolution,[],[f100,f110,f228,f76])).
% 3.66/0.88  fof(f638,plain,(
% 3.66/0.88    spl7_14 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_15),
% 3.66/0.88    inference(avatar_split_clause,[],[f444,f230,f108,f103,f98,f226])).
% 3.66/0.88  fof(f103,plain,(
% 3.66/0.88    spl7_3 <=> v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 3.66/0.88  fof(f444,plain,(
% 3.66/0.88    v1_partfun1(sK3,sK0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_15)),
% 3.66/0.88    inference(unit_resulting_resolution,[],[f100,f105,f110,f231,f89])).
% 3.66/0.88  fof(f89,plain,(
% 3.66/0.88    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 3.66/0.88    inference(duplicate_literal_removal,[],[f50])).
% 3.66/0.88  fof(f50,plain,(
% 3.66/0.88    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f16])).
% 3.66/0.88  fof(f16,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.66/0.88    inference(flattening,[],[f15])).
% 3.66/0.88  fof(f15,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.66/0.88    inference(ennf_transformation,[],[f6])).
% 3.66/0.88  fof(f6,axiom,(
% 3.66/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.66/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 3.66/0.88  fof(f231,plain,(
% 3.66/0.88    k1_xboole_0 != k1_enumset1(sK1,sK1,sK1) | spl7_15),
% 3.66/0.88    inference(avatar_component_clause,[],[f230])).
% 3.66/0.88  fof(f105,plain,(
% 3.66/0.88    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1)) | ~spl7_3),
% 3.66/0.88    inference(avatar_component_clause,[],[f103])).
% 3.66/0.88  fof(f510,plain,(
% 3.66/0.88    spl7_22 | ~spl7_14 | ~spl7_2 | ~spl7_4),
% 3.66/0.88    inference(avatar_split_clause,[],[f304,f108,f98,f226,f508])).
% 3.66/0.88  fof(f304,plain,(
% 3.66/0.88    ( ! [X0] : (~v1_partfun1(sK3,sK0) | ~v1_partfun1(X0,sK0) | sK3 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(X0)) ) | (~spl7_2 | ~spl7_4)),
% 3.66/0.88    inference(subsumption_resolution,[],[f271,f246])).
% 3.66/0.88  fof(f246,plain,(
% 3.66/0.88    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | r1_partfun1(X0,sK3) | ~v1_funct_1(X0)) ) | (~spl7_2 | ~spl7_4)),
% 3.66/0.88    inference(resolution,[],[f162,f110])).
% 3.66/0.88  fof(f162,plain,(
% 3.66/0.88    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,k1_enumset1(X4,X4,X4)))) | r1_partfun1(X5,sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,k1_enumset1(X4,X4,X4)))) | ~v1_funct_1(X5)) ) | ~spl7_2),
% 3.66/0.88    inference(resolution,[],[f77,f100])).
% 3.66/0.88  fof(f77,plain,(
% 3.66/0.88    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1)))) | r1_partfun1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_enumset1(X1,X1,X1)))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(definition_unfolding,[],[f67,f68,f68])).
% 3.66/0.88  fof(f67,plain,(
% 3.66/0.88    ( ! [X2,X0,X3,X1] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f24])).
% 3.66/0.88  fof(f24,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2))),
% 3.66/0.88    inference(flattening,[],[f23])).
% 3.66/0.88  fof(f23,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (! [X3] : (r1_partfun1(X2,X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) | ~v1_funct_1(X2)))),
% 3.66/0.88    inference(ennf_transformation,[],[f7])).
% 3.66/0.88  fof(f7,axiom,(
% 3.66/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X3)) => r1_partfun1(X2,X3)))),
% 3.66/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_partfun1)).
% 3.66/0.88  fof(f271,plain,(
% 3.66/0.88    ( ! [X0] : (~v1_partfun1(sK3,sK0) | ~v1_partfun1(X0,sK0) | ~r1_partfun1(X0,sK3) | sK3 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)))) | ~v1_funct_1(X0)) ) | (~spl7_2 | ~spl7_4)),
% 3.66/0.88    inference(resolution,[],[f166,f110])).
% 3.66/0.88  fof(f166,plain,(
% 3.66/0.88    ( ! [X4,X5,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_partfun1(sK3,X4) | ~v1_partfun1(X3,X4) | ~r1_partfun1(X3,sK3) | sK3 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X3)) ) | ~spl7_2),
% 3.66/0.88    inference(resolution,[],[f54,f100])).
% 3.66/0.88  fof(f54,plain,(
% 3.66/0.88    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f20])).
% 3.66/0.88  fof(f20,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.66/0.88    inference(flattening,[],[f19])).
% 3.66/0.88  fof(f19,plain,(
% 3.66/0.88    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.66/0.88    inference(ennf_transformation,[],[f8])).
% 3.66/0.88  fof(f8,axiom,(
% 3.66/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 3.66/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 3.66/0.88  fof(f303,plain,(
% 3.66/0.88    spl7_16 | ~spl7_2 | ~spl7_4 | ~spl7_10 | ~spl7_14),
% 3.66/0.88    inference(avatar_split_clause,[],[f258,f226,f168,f108,f98,f300])).
% 3.66/0.88  fof(f168,plain,(
% 3.66/0.88    spl7_10 <=> r1_partfun1(sK3,sK3)),
% 3.66/0.88    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 3.66/0.88  fof(f258,plain,(
% 3.66/0.88    r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | (~spl7_2 | ~spl7_4 | ~spl7_10 | ~spl7_14)),
% 3.66/0.88    inference(forward_demodulation,[],[f249,f253])).
% 3.66/0.88  fof(f253,plain,(
% 3.66/0.88    k1_enumset1(sK3,sK3,sK3) = k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3) | (~spl7_2 | ~spl7_4 | ~spl7_14)),
% 3.66/0.88    inference(unit_resulting_resolution,[],[f100,f110,f228,f76])).
% 3.66/0.88  fof(f249,plain,(
% 3.66/0.88    r2_hidden(sK3,k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK3)) | (~spl7_2 | ~spl7_4 | ~spl7_10 | ~spl7_14)),
% 3.66/0.88    inference(unit_resulting_resolution,[],[f100,f100,f170,f110,f110,f228,f83])).
% 3.66/0.88  fof(f83,plain,(
% 3.66/0.88    ( ! [X2,X0,X8,X1] : (~v1_funct_1(X8) | ~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(X8,k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(equality_resolution,[],[f82])).
% 3.66/0.88  fof(f82,plain,(
% 3.66/0.88    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8) | k5_partfun1(X0,X1,X2) != X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(equality_resolution,[],[f60])).
% 3.66/0.88  fof(f60,plain,(
% 3.66/0.88    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X2,X8) | ~v1_partfun1(X8,X0) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X8) | k5_partfun1(X0,X1,X2) != X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.66/0.88    inference(cnf_transformation,[],[f36])).
% 3.66/0.88  fof(f170,plain,(
% 3.66/0.88    r1_partfun1(sK3,sK3) | ~spl7_10),
% 3.66/0.88    inference(avatar_component_clause,[],[f168])).
% 3.66/0.88  fof(f184,plain,(
% 3.66/0.88    spl7_11 | ~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5),
% 3.66/0.88    inference(avatar_split_clause,[],[f158,f113,f108,f98,f93,f181])).
% 3.66/0.88  fof(f158,plain,(
% 3.66/0.88    r1_partfun1(sK2,sK3) | (~spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5)),
% 3.66/0.88    inference(unit_resulting_resolution,[],[f95,f100,f115,f110,f77])).
% 3.66/0.88  fof(f171,plain,(
% 3.66/0.88    spl7_10 | ~spl7_2 | ~spl7_4),
% 3.66/0.88    inference(avatar_split_clause,[],[f157,f108,f98,f168])).
% 3.66/0.88  fof(f157,plain,(
% 3.66/0.88    r1_partfun1(sK3,sK3) | (~spl7_2 | ~spl7_4)),
% 3.66/0.88    inference(unit_resulting_resolution,[],[f100,f100,f110,f110,f77])).
% 3.66/0.88  fof(f121,plain,(
% 3.66/0.88    ~spl7_6),
% 3.66/0.88    inference(avatar_split_clause,[],[f69,f118])).
% 3.66/0.88  fof(f69,plain,(
% 3.66/0.88    k5_partfun1(sK0,k1_enumset1(sK1,sK1,sK1),sK2) != k1_enumset1(sK3,sK3,sK3)),
% 3.66/0.88    inference(definition_unfolding,[],[f42,f68,f68])).
% 3.66/0.88  fof(f42,plain,(
% 3.66/0.88    k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3)),
% 3.66/0.88    inference(cnf_transformation,[],[f27])).
% 3.66/0.88  fof(f27,plain,(
% 3.66/0.88    (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2)),
% 3.66/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f26,f25])).
% 3.66/0.88  fof(f25,plain,(
% 3.66/0.88    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => (? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_1(sK2))),
% 3.66/0.88    introduced(choice_axiom,[])).
% 3.66/0.88  fof(f26,plain,(
% 3.66/0.88    ? [X3] : (k1_tarski(X3) != k5_partfun1(sK0,k1_tarski(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(X3,sK0,k1_tarski(sK1)) & v1_funct_1(X3)) => (k5_partfun1(sK0,k1_tarski(sK1),sK2) != k1_tarski(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) & v1_funct_2(sK3,sK0,k1_tarski(sK1)) & v1_funct_1(sK3))),
% 3.66/0.88    introduced(choice_axiom,[])).
% 3.66/0.88  fof(f13,plain,(
% 3.66/0.88    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2))),
% 3.66/0.88    inference(flattening,[],[f12])).
% 3.66/0.88  fof(f12,plain,(
% 3.66/0.88    ? [X0,X1,X2] : (? [X3] : (k5_partfun1(X0,k1_tarski(X1),X2) != k1_tarski(X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)))),
% 3.66/0.88    inference(ennf_transformation,[],[f11])).
% 3.66/0.88  fof(f11,negated_conjecture,(
% 3.66/0.88    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 3.66/0.88    inference(negated_conjecture,[],[f10])).
% 3.66/0.88  fof(f10,conjecture,(
% 3.66/0.88    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => k5_partfun1(X0,k1_tarski(X1),X2) = k1_tarski(X3)))),
% 3.66/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_2)).
% 3.66/0.88  fof(f116,plain,(
% 3.66/0.88    spl7_5),
% 3.66/0.88    inference(avatar_split_clause,[],[f72,f113])).
% 3.66/0.88  fof(f72,plain,(
% 3.66/0.88    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 3.66/0.88    inference(definition_unfolding,[],[f38,f68])).
% 3.66/0.88  fof(f38,plain,(
% 3.66/0.88    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 3.66/0.88    inference(cnf_transformation,[],[f27])).
% 3.66/0.88  fof(f111,plain,(
% 3.66/0.88    spl7_4),
% 3.66/0.88    inference(avatar_split_clause,[],[f70,f108])).
% 3.66/0.88  fof(f70,plain,(
% 3.66/0.88    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))))),
% 3.66/0.88    inference(definition_unfolding,[],[f41,f68])).
% 3.66/0.88  fof(f41,plain,(
% 3.66/0.88    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 3.66/0.88    inference(cnf_transformation,[],[f27])).
% 3.66/0.88  fof(f106,plain,(
% 3.66/0.88    spl7_3),
% 3.66/0.88    inference(avatar_split_clause,[],[f71,f103])).
% 3.66/0.88  fof(f71,plain,(
% 3.66/0.88    v1_funct_2(sK3,sK0,k1_enumset1(sK1,sK1,sK1))),
% 3.66/0.88    inference(definition_unfolding,[],[f40,f68])).
% 3.66/0.88  fof(f40,plain,(
% 3.66/0.88    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 3.66/0.88    inference(cnf_transformation,[],[f27])).
% 3.66/0.88  fof(f101,plain,(
% 3.66/0.88    spl7_2),
% 3.66/0.88    inference(avatar_split_clause,[],[f39,f98])).
% 3.66/0.88  fof(f39,plain,(
% 3.66/0.88    v1_funct_1(sK3)),
% 3.66/0.88    inference(cnf_transformation,[],[f27])).
% 3.66/0.88  fof(f96,plain,(
% 3.66/0.88    spl7_1),
% 3.66/0.88    inference(avatar_split_clause,[],[f37,f93])).
% 3.66/0.88  fof(f37,plain,(
% 3.66/0.88    v1_funct_1(sK2)),
% 3.66/0.88    inference(cnf_transformation,[],[f27])).
% 3.66/0.88  % SZS output end Proof for theBenchmark
% 3.66/0.88  % (4217)------------------------------
% 3.66/0.88  % (4217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.88  % (4217)Termination reason: Refutation
% 3.66/0.88  
% 3.66/0.88  % (4217)Memory used [KB]: 13048
% 3.66/0.88  % (4217)Time elapsed: 0.446 s
% 3.66/0.88  % (4217)------------------------------
% 3.66/0.88  % (4217)------------------------------
% 3.66/0.89  % (4196)Success in time 0.509 s
%------------------------------------------------------------------------------
