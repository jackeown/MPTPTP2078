%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 464 expanded)
%              Number of leaves         :   37 ( 178 expanded)
%              Depth                    :   17
%              Number of atoms          :  992 (2850 expanded)
%              Number of equality atoms :  249 ( 951 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f493,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f105,f110,f115,f120,f125,f143,f162,f167,f172,f183,f184,f196,f214,f217,f246,f255,f291,f296,f336,f355,f356,f387,f424,f436,f463,f464,f492])).

fof(f492,plain,
    ( ~ spl7_1
    | spl7_7
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_22
    | spl7_24
    | spl7_34 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | ~ spl7_1
    | spl7_7
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_22
    | spl7_24
    | spl7_34 ),
    inference(subsumption_resolution,[],[f490,f353])).

fof(f353,plain,
    ( sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | spl7_34 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl7_34
  <=> sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f490,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_1
    | spl7_7
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_22
    | spl7_24 ),
    inference(subsumption_resolution,[],[f465,f244])).

fof(f244,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | spl7_24 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl7_24
  <=> r2_hidden(sK4(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f465,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_1
    | spl7_7
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f257,f236])).

fof(f236,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f235])).

% (11480)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f235,plain,
    ( spl7_22
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f257,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | ~ v1_relat_1(sK3)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_1
    | spl7_7
    | ~ spl7_17
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f256,f104])).

fof(f104,plain,
    ( sK3 != k2_funct_1(sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_7
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f256,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | sK3 = k2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_1
    | ~ spl7_17
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f250,f176])).

fof(f176,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_17
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f250,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | sK1 != k1_relat_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_1
    | ~ spl7_21 ),
    inference(resolution,[],[f220,f74])).

fof(f74,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f220,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | r2_hidden(sK4(sK2,X1),sK1)
        | k1_relat_1(X1) != sK1
        | k2_funct_1(sK2) = X1
        | ~ v1_relat_1(X1)
        | sK4(sK2,X1) = k1_funct_1(sK2,sK5(sK2,X1)) )
    | ~ spl7_21 ),
    inference(resolution,[],[f213,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X2,X1,X0)
      | k1_funct_1(X0,X3) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(f213,plain,
    ( ! [X2] :
        ( ~ sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2)
        | k2_funct_1(sK2) = X2
        | r2_hidden(sK4(sK2,X2),sK1)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl7_21
  <=> ! [X2] :
        ( r2_hidden(sK4(sK2,X2),sK1)
        | k2_funct_1(sK2) = X2
        | ~ sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2)
        | k1_relat_1(X2) != sK1
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f464,plain,
    ( sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK4(sK2,sK3) != k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3)))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f463,plain,
    ( spl7_23
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | spl7_23
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f461,f245])).

fof(f245,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f243])).

fof(f461,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | spl7_23
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f358,f240])).

fof(f240,plain,
    ( ~ r2_hidden(sK5(sK2,sK3),sK0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl7_23
  <=> r2_hidden(sK5(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f358,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ r2_hidden(sK4(sK2,sK3),sK1)
    | ~ spl7_28 ),
    inference(superposition,[],[f54,f295])).

fof(f295,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl7_28
  <=> sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f54,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK3,X4),sK0)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK3,X4) != X5
      | r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) )
                     => ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) ) )
                    & ( ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) )
                     => ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) ) ) )
                & v2_funct_1(X2)
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) )
                   => ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) ) )
                  & ( ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) )
                   => ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) ) ) )
              & v2_funct_1(X2)
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_2)).

fof(f436,plain,
    ( ~ spl7_23
    | spl7_24
    | ~ spl7_34 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | ~ spl7_23
    | spl7_24
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f428,f244])).

fof(f428,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | ~ spl7_23
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f364,f241])).

fof(f241,plain,
    ( r2_hidden(sK5(sK2,sK3),sK0)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f239])).

fof(f364,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | ~ r2_hidden(sK5(sK2,sK3),sK0)
    | ~ spl7_34 ),
    inference(superposition,[],[f56,f354])).

fof(f354,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f352])).

fof(f56,plain,(
    ! [X5] :
      ( r2_hidden(k1_funct_1(sK2,X5),sK1)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK2,X5) != X4
      | r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f424,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_34
    | ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_34
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f422,f386])).

fof(f386,plain,
    ( sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl7_35
  <=> sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f422,plain,
    ( ~ sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f310,f354])).

fof(f310,plain,
    ( sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f309,f104])).

fof(f309,plain,
    ( sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f308,f74])).

fof(f308,plain,
    ( ~ v1_funct_1(sK3)
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f307,f236])).

fof(f307,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f300,f176])).

fof(f300,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_23 ),
    inference(resolution,[],[f241,f233])).

fof(f233,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK2,X2),sK0)
        | k1_relat_1(X2) != sK1
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | sK4(sK2,X2) != k1_funct_1(sK2,sK5(sK2,X2))
        | ~ sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2)
        | k2_funct_1(sK2) = X2 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f201,f209])).

fof(f209,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl7_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f201,plain,
    ( ! [X2] :
        ( k1_relat_1(X2) != sK1
        | ~ r2_hidden(sK5(sK2,X2),sK0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(sK2)
        | sK4(sK2,X2) != k1_funct_1(sK2,sK5(sK2,X2))
        | ~ sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2)
        | k2_funct_1(sK2) = X2 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_19 ),
    inference(forward_demodulation,[],[f200,f142])).

fof(f142,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl7_12
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f200,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK2,X2),sK0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_relat_1(X2) != k2_relat_1(sK2)
        | ~ v1_relat_1(sK2)
        | sK4(sK2,X2) != k1_funct_1(sK2,sK5(sK2,X2))
        | ~ sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2)
        | k2_funct_1(sK2) = X2 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f199,f79])).

fof(f79,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f199,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK2,X2),sK0)
        | ~ v2_funct_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_relat_1(X2) != k2_relat_1(sK2)
        | ~ v1_relat_1(sK2)
        | sK4(sK2,X2) != k1_funct_1(sK2,sK5(sK2,X2))
        | ~ sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2)
        | k2_funct_1(sK2) = X2 )
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f198,f84])).

fof(f84,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f198,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK2,X2),sK0)
        | ~ v1_funct_1(sK2)
        | ~ v2_funct_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_relat_1(X2) != k2_relat_1(sK2)
        | ~ v1_relat_1(sK2)
        | sK4(sK2,X2) != k1_funct_1(sK2,sK5(sK2,X2))
        | ~ sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2)
        | k2_funct_1(sK2) = X2 )
    | ~ spl7_19 ),
    inference(superposition,[],[f37,f188])).

fof(f188,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl7_19
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | sK4(X0,X1) != k1_funct_1(X0,sK5(X0,X1))
      | ~ sP6(sK5(X0,X1),sK4(X0,X1),X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f387,plain,
    ( spl7_35
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f376,f293,f243,f140,f384])).

fof(f376,plain,
    ( sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2)
    | ~ spl7_12
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f375,f245])).

fof(f375,plain,
    ( ~ r2_hidden(sK4(sK2,sK3),sK1)
    | sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2)
    | ~ spl7_12
    | ~ spl7_28 ),
    inference(superposition,[],[f360,f142])).

% (11475)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f360,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK2,sK3),k2_relat_1(X1))
        | sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,X1) )
    | ~ spl7_28 ),
    inference(superposition,[],[f63,f295])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP6(k1_funct_1(X1,X2),X2,X1,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | k1_funct_1(X1,X2) != X3
      | sP6(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f356,plain,
    ( sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3))
    | sK5(sK2,sK3) != k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3)))
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f355,plain,
    ( spl7_34
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_22
    | spl7_28 ),
    inference(avatar_split_clause,[],[f350,f293,f235,f208,f174,f140,f102,f82,f77,f72,f352])).

fof(f350,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_22
    | spl7_28 ),
    inference(subsumption_resolution,[],[f277,f294])).

fof(f294,plain,
    ( sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3))
    | spl7_28 ),
    inference(avatar_component_clause,[],[f293])).

fof(f277,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f276,f104])).

fof(f276,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK3 = k2_funct_1(sK2)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f275,f176])).

fof(f275,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK1 != k1_relat_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f273,f236])).

fof(f273,plain,
    ( ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK1 != k1_relat_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(resolution,[],[f231,f74])).

fof(f231,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1))
        | k1_relat_1(X1) != sK1
        | k2_funct_1(sK2) = X1
        | sK4(sK2,X1) = k1_funct_1(sK2,sK5(sK2,X1)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(resolution,[],[f223,f36])).

fof(f223,plain,
    ( ! [X3] :
        ( ~ sP6(sK5(sK2,X3),sK4(sK2,X3),X3,sK2)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
        | sK1 != k1_relat_1(X3)
        | k2_funct_1(sK2) = X3 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f150,f209])).

fof(f150,plain,
    ( ! [X3] :
        ( sK1 != k1_relat_1(X3)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(sK2)
        | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
        | ~ sP6(sK5(sK2,X3),sK4(sK2,X3),X3,sK2)
        | k2_funct_1(sK2) = X3 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f149,f79])).

fof(f149,plain,
    ( ! [X3] :
        ( sK1 != k1_relat_1(X3)
        | ~ v2_funct_1(sK2)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(sK2)
        | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
        | ~ sP6(sK5(sK2,X3),sK4(sK2,X3),X3,sK2)
        | k2_funct_1(sK2) = X3 )
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f146,f84])).

fof(f146,plain,
    ( ! [X3] :
        ( sK1 != k1_relat_1(X3)
        | ~ v1_funct_1(sK2)
        | ~ v2_funct_1(sK2)
        | ~ v1_relat_1(X3)
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(sK2)
        | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3))
        | ~ sP6(sK5(sK2,X3),sK4(sK2,X3),X3,sK2)
        | k2_funct_1(sK2) = X3 )
    | ~ spl7_12 ),
    inference(superposition,[],[f41,f142])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1))
      | ~ sP6(sK5(X0,X1),sK4(X0,X1),X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f336,plain,
    ( spl7_33
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f306,f239,f333])).

fof(f333,plain,
    ( spl7_33
  <=> sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f306,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3)))
    | ~ spl7_23 ),
    inference(resolution,[],[f241,f55])).

fof(f55,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK3,k1_funct_1(sK2,X5)) = X5 ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK2,X5) != X4
      | k1_funct_1(sK3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f296,plain,
    ( spl7_28
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22
    | spl7_23 ),
    inference(avatar_split_clause,[],[f286,f239,f235,f208,f186,f174,f140,f102,f82,f77,f72,f293])).

fof(f286,plain,
    ( sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22
    | spl7_23 ),
    inference(subsumption_resolution,[],[f270,f236])).

fof(f270,plain,
    ( ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | spl7_23 ),
    inference(subsumption_resolution,[],[f269,f104])).

fof(f269,plain,
    ( ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK3 = k2_funct_1(sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | spl7_23 ),
    inference(subsumption_resolution,[],[f268,f176])).

fof(f268,plain,
    ( ~ v1_relat_1(sK3)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK1 != k1_relat_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_20
    | spl7_23 ),
    inference(subsumption_resolution,[],[f266,f240])).

fof(f266,plain,
    ( ~ v1_relat_1(sK3)
    | r2_hidden(sK5(sK2,sK3),sK0)
    | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))
    | sK1 != k1_relat_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(resolution,[],[f232,f74])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK5(sK2,X0),sK0)
        | sK5(sK2,X0) = k1_funct_1(X0,sK4(sK2,X0))
        | k1_relat_1(X0) != sK1
        | k2_funct_1(sK2) = X0 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_20 ),
    inference(forward_demodulation,[],[f230,f188])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | sK5(sK2,X0) = k1_funct_1(X0,sK4(sK2,X0))
        | k1_relat_1(X0) != sK1
        | k2_funct_1(sK2) = X0
        | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(resolution,[],[f223,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X2,X1,X0)
      | r2_hidden(X3,k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f291,plain,
    ( spl7_27
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f285,f243,f288])).

fof(f288,plain,
    ( spl7_27
  <=> sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f285,plain,
    ( sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3)))
    | ~ spl7_24 ),
    inference(resolution,[],[f245,f53])).

fof(f53,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK2,k1_funct_1(sK3,X4)) = X4 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK1)
      | k1_funct_1(sK3,X4) != X5
      | k1_funct_1(sK2,X5) = X4 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f255,plain,
    ( ~ spl7_9
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | ~ spl7_9
    | spl7_22 ),
    inference(resolution,[],[f247,f114])).

fof(f114,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f247,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_22 ),
    inference(resolution,[],[f237,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f237,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f235])).

fof(f246,plain,
    ( ~ spl7_22
    | spl7_23
    | spl7_24
    | ~ spl7_1
    | spl7_7
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f227,f212,f186,f174,f102,f72,f243,f239,f235])).

fof(f227,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | r2_hidden(sK5(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | spl7_7
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f226,f176])).

fof(f226,plain,
    ( r2_hidden(sK4(sK2,sK3),sK1)
    | sK1 != k1_relat_1(sK3)
    | r2_hidden(sK5(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | spl7_7
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f224,f104])).

fof(f224,plain,
    ( sK3 = k2_funct_1(sK2)
    | r2_hidden(sK4(sK2,sK3),sK1)
    | sK1 != k1_relat_1(sK3)
    | r2_hidden(sK5(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(resolution,[],[f221,f74])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k2_funct_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),sK1)
        | k1_relat_1(X0) != sK1
        | r2_hidden(sK5(sK2,X0),sK0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_19
    | ~ spl7_21 ),
    inference(forward_demodulation,[],[f219,f188])).

fof(f219,plain,
    ( ! [X0] :
        ( k2_funct_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),sK1)
        | k1_relat_1(X0) != sK1
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) )
    | ~ spl7_21 ),
    inference(resolution,[],[f213,f35])).

fof(f217,plain,
    ( ~ spl7_11
    | spl7_20 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl7_11
    | spl7_20 ),
    inference(resolution,[],[f215,f124])).

fof(f124,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl7_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f215,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_20 ),
    inference(resolution,[],[f210,f44])).

fof(f210,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f214,plain,
    ( ~ spl7_20
    | spl7_21
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f148,f140,f82,f77,f212,f208])).

fof(f148,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK2,X2),sK1)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_relat_1(X2) != sK1
        | ~ v1_relat_1(sK2)
        | ~ sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2)
        | k2_funct_1(sK2) = X2 )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f147,f79])).

fof(f147,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK2,X2),sK1)
        | ~ v2_funct_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_relat_1(X2) != sK1
        | ~ v1_relat_1(sK2)
        | ~ sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2)
        | k2_funct_1(sK2) = X2 )
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f145,f84])).

fof(f145,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(sK2,X2),sK1)
        | ~ v1_funct_1(sK2)
        | ~ v2_funct_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k1_relat_1(X2) != sK1
        | ~ v1_relat_1(sK2)
        | ~ sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2)
        | k2_funct_1(sK2) = X2 )
    | ~ spl7_12 ),
    inference(superposition,[],[f40,f142])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP6(sK5(X0,X1),sK4(X0,X1),X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f196,plain,
    ( spl7_19
    | ~ spl7_15
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f192,f180,f164,f186])).

fof(f164,plain,
    ( spl7_15
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f180,plain,
    ( spl7_18
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f192,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_15
    | ~ spl7_18 ),
    inference(superposition,[],[f182,f166])).

fof(f166,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f164])).

fof(f182,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f184,plain,
    ( k1_relset_1(sK1,sK0,sK3) != k1_relat_1(sK3)
    | sK1 != k1_relset_1(sK1,sK0,sK3)
    | sK1 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f183,plain,
    ( spl7_18
    | spl7_5
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f137,f122,f107,f92,f180])).

fof(f92,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f107,plain,
    ( spl7_8
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f137,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | spl7_5
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f136,f109])).

fof(f109,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f136,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | spl7_5
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f133,f94])).

fof(f94,plain,
    ( k1_xboole_0 != sK1
    | spl7_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f133,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_11 ),
    inference(resolution,[],[f124,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f172,plain,
    ( spl7_16
    | spl7_4
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f131,f112,f97,f87,f169])).

fof(f169,plain,
    ( spl7_16
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f87,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f97,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f131,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | spl7_4
    | ~ spl7_6
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f130,f99])).

fof(f99,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f130,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | spl7_4
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f127,f89])).

fof(f89,plain,
    ( k1_xboole_0 != sK0
    | spl7_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f127,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl7_9 ),
    inference(resolution,[],[f114,f52])).

fof(f167,plain,
    ( spl7_15
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f135,f122,f164])).

fof(f135,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl7_11 ),
    inference(resolution,[],[f124,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f162,plain,
    ( spl7_14
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f129,f112,f159])).

fof(f159,plain,
    ( spl7_14
  <=> k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f129,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)
    | ~ spl7_9 ),
    inference(resolution,[],[f114,f45])).

fof(f143,plain,
    ( spl7_12
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f138,f122,f117,f140])).

fof(f117,plain,
    ( spl7_10
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f138,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f134,f119])).

fof(f119,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f134,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl7_11 ),
    inference(resolution,[],[f124,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f125,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f31,f122])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f120,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f24,f117])).

fof(f24,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f115,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f23,f112])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f110,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f30,f107])).

fof(f30,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f28,f102])).

fof(f28,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f22,f97])).

fof(f22,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f95,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f27,f92])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f90,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f26,f87])).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f85,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f29,f82])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f25,f77])).

fof(f25,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f21,f72])).

fof(f21,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (11474)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (11479)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (11484)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (11476)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (11474)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (11482)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (11487)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (11482)Refutation not found, incomplete strategy% (11482)------------------------------
% 0.21/0.49  % (11482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f493,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f75,f80,f85,f90,f95,f100,f105,f110,f115,f120,f125,f143,f162,f167,f172,f183,f184,f196,f214,f217,f246,f255,f291,f296,f336,f355,f356,f387,f424,f436,f463,f464,f492])).
% 0.21/0.49  fof(f492,plain,(
% 0.21/0.49    ~spl7_1 | spl7_7 | ~spl7_17 | ~spl7_21 | ~spl7_22 | spl7_24 | spl7_34),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f491])).
% 0.21/0.49  fof(f491,plain,(
% 0.21/0.49    $false | (~spl7_1 | spl7_7 | ~spl7_17 | ~spl7_21 | ~spl7_22 | spl7_24 | spl7_34)),
% 0.21/0.49    inference(subsumption_resolution,[],[f490,f353])).
% 0.21/0.49  fof(f353,plain,(
% 0.21/0.49    sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | spl7_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f352])).
% 0.21/0.49  fof(f352,plain,(
% 0.21/0.49    spl7_34 <=> sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.49  fof(f490,plain,(
% 0.21/0.49    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | (~spl7_1 | spl7_7 | ~spl7_17 | ~spl7_21 | ~spl7_22 | spl7_24)),
% 0.21/0.49    inference(subsumption_resolution,[],[f465,f244])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK2,sK3),sK1) | spl7_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f243])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    spl7_24 <=> r2_hidden(sK4(sK2,sK3),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.49  fof(f465,plain,(
% 0.21/0.49    r2_hidden(sK4(sK2,sK3),sK1) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | (~spl7_1 | spl7_7 | ~spl7_17 | ~spl7_21 | ~spl7_22)),
% 0.21/0.49    inference(subsumption_resolution,[],[f257,f236])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl7_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f235])).
% 0.21/0.49  % (11480)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    spl7_22 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    r2_hidden(sK4(sK2,sK3),sK1) | ~v1_relat_1(sK3) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | (~spl7_1 | spl7_7 | ~spl7_17 | ~spl7_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f256,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    sK3 != k2_funct_1(sK2) | spl7_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl7_7 <=> sK3 = k2_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    r2_hidden(sK4(sK2,sK3),sK1) | sK3 = k2_funct_1(sK2) | ~v1_relat_1(sK3) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | (~spl7_1 | ~spl7_17 | ~spl7_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f250,f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    sK1 = k1_relat_1(sK3) | ~spl7_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    spl7_17 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    r2_hidden(sK4(sK2,sK3),sK1) | sK1 != k1_relat_1(sK3) | sK3 = k2_funct_1(sK2) | ~v1_relat_1(sK3) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | (~spl7_1 | ~spl7_21)),
% 0.21/0.49    inference(resolution,[],[f220,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    v1_funct_1(sK3) | ~spl7_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl7_1 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(X1) | r2_hidden(sK4(sK2,X1),sK1) | k1_relat_1(X1) != sK1 | k2_funct_1(sK2) = X1 | ~v1_relat_1(X1) | sK4(sK2,X1) = k1_funct_1(sK2,sK5(sK2,X1))) ) | ~spl7_21),
% 0.21/0.49    inference(resolution,[],[f213,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sP6(X3,X2,X1,X0) | k1_funct_1(X0,X3) = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    ( ! [X2] : (~sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2) | k2_funct_1(sK2) = X2 | r2_hidden(sK4(sK2,X2),sK1) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) ) | ~spl7_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f212])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    spl7_21 <=> ! [X2] : (r2_hidden(sK4(sK2,X2),sK1) | k2_funct_1(sK2) = X2 | ~sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2) | k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.49  fof(f464,plain,(
% 0.21/0.49    sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3)) | sK4(sK2,sK3) != k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3))) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f463,plain,(
% 0.21/0.49    spl7_23 | ~spl7_24 | ~spl7_28),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f462])).
% 0.21/0.49  fof(f462,plain,(
% 0.21/0.49    $false | (spl7_23 | ~spl7_24 | ~spl7_28)),
% 0.21/0.49    inference(subsumption_resolution,[],[f461,f245])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    r2_hidden(sK4(sK2,sK3),sK1) | ~spl7_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f243])).
% 0.21/0.49  fof(f461,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK2,sK3),sK1) | (spl7_23 | ~spl7_28)),
% 0.21/0.49    inference(subsumption_resolution,[],[f358,f240])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    ~r2_hidden(sK5(sK2,sK3),sK0) | spl7_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f239])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    spl7_23 <=> r2_hidden(sK5(sK2,sK3),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.49  fof(f358,plain,(
% 0.21/0.49    r2_hidden(sK5(sK2,sK3),sK0) | ~r2_hidden(sK4(sK2,sK3),sK1) | ~spl7_28),
% 0.21/0.49    inference(superposition,[],[f54,f295])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl7_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f293])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    spl7_28 <=> sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X4] : (r2_hidden(k1_funct_1(sK3,X4),sK0) | ~r2_hidden(X4,sK1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r2_hidden(X4,sK1) | k1_funct_1(sK3,X4) != X5 | r2_hidden(X5,sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | (k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0))) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | (k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_2)).
% 0.21/0.49  fof(f436,plain,(
% 0.21/0.49    ~spl7_23 | spl7_24 | ~spl7_34),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f435])).
% 0.21/0.49  fof(f435,plain,(
% 0.21/0.49    $false | (~spl7_23 | spl7_24 | ~spl7_34)),
% 0.21/0.49    inference(subsumption_resolution,[],[f428,f244])).
% 0.21/0.49  fof(f428,plain,(
% 0.21/0.49    r2_hidden(sK4(sK2,sK3),sK1) | (~spl7_23 | ~spl7_34)),
% 0.21/0.49    inference(subsumption_resolution,[],[f364,f241])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    r2_hidden(sK5(sK2,sK3),sK0) | ~spl7_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f239])).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    r2_hidden(sK4(sK2,sK3),sK1) | ~r2_hidden(sK5(sK2,sK3),sK0) | ~spl7_34),
% 0.21/0.49    inference(superposition,[],[f56,f354])).
% 0.21/0.49  fof(f354,plain,(
% 0.21/0.49    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | ~spl7_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f352])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X5] : (r2_hidden(k1_funct_1(sK2,X5),sK1) | ~r2_hidden(X5,sK0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r2_hidden(X5,sK0) | k1_funct_1(sK2,X5) != X4 | r2_hidden(X4,sK1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f424,plain,(
% 0.21/0.49    ~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | ~spl7_22 | ~spl7_23 | ~spl7_34 | ~spl7_35),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f423])).
% 0.21/0.49  fof(f423,plain,(
% 0.21/0.49    $false | (~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | ~spl7_22 | ~spl7_23 | ~spl7_34 | ~spl7_35)),
% 0.21/0.49    inference(subsumption_resolution,[],[f422,f386])).
% 0.21/0.49  fof(f386,plain,(
% 0.21/0.49    sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2) | ~spl7_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f384])).
% 0.21/0.49  fof(f384,plain,(
% 0.21/0.49    spl7_35 <=> sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.49  fof(f422,plain,(
% 0.21/0.49    ~sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2) | (~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | ~spl7_22 | ~spl7_23 | ~spl7_34)),
% 0.21/0.49    inference(subsumption_resolution,[],[f310,f354])).
% 0.21/0.49  fof(f310,plain,(
% 0.21/0.49    sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | ~sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2) | (~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | ~spl7_22 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f309,f104])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | ~sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2) | sK3 = k2_funct_1(sK2) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | ~spl7_22 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f308,f74])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    ~v1_funct_1(sK3) | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | ~sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2) | sK3 = k2_funct_1(sK2) | (~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | ~spl7_22 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f307,f236])).
% 0.21/0.49  fof(f307,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | ~sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2) | sK3 = k2_funct_1(sK2) | (~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | ~spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f300,f176])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | ~sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2) | sK3 = k2_funct_1(sK2) | (~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_19 | ~spl7_20 | ~spl7_23)),
% 0.21/0.49    inference(resolution,[],[f241,f233])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ( ! [X2] : (~r2_hidden(sK5(sK2,X2),sK0) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2) | ~v1_funct_1(X2) | sK4(sK2,X2) != k1_funct_1(sK2,sK5(sK2,X2)) | ~sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2) | k2_funct_1(sK2) = X2) ) | (~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_19 | ~spl7_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f201,f209])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl7_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f208])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    spl7_20 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~r2_hidden(sK5(sK2,X2),sK0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(sK2) | sK4(sK2,X2) != k1_funct_1(sK2,sK5(sK2,X2)) | ~sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2) | k2_funct_1(sK2) = X2) ) | (~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_19)),
% 0.21/0.49    inference(forward_demodulation,[],[f200,f142])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    sK1 = k2_relat_1(sK2) | ~spl7_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl7_12 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ( ! [X2] : (~r2_hidden(sK5(sK2,X2),sK0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | sK4(sK2,X2) != k1_funct_1(sK2,sK5(sK2,X2)) | ~sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2) | k2_funct_1(sK2) = X2) ) | (~spl7_2 | ~spl7_3 | ~spl7_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f199,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    v2_funct_1(sK2) | ~spl7_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl7_2 <=> v2_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ( ! [X2] : (~r2_hidden(sK5(sK2,X2),sK0) | ~v2_funct_1(sK2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | sK4(sK2,X2) != k1_funct_1(sK2,sK5(sK2,X2)) | ~sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2) | k2_funct_1(sK2) = X2) ) | (~spl7_3 | ~spl7_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f198,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v1_funct_1(sK2) | ~spl7_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl7_3 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    ( ! [X2] : (~r2_hidden(sK5(sK2,X2),sK0) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != k2_relat_1(sK2) | ~v1_relat_1(sK2) | sK4(sK2,X2) != k1_funct_1(sK2,sK5(sK2,X2)) | ~sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2) | k2_funct_1(sK2) = X2) ) | ~spl7_19),
% 0.21/0.49    inference(superposition,[],[f37,f188])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | ~spl7_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f186])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    spl7_19 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_relat_1(X0) | sK4(X0,X1) != k1_funct_1(X0,sK5(X0,X1)) | ~sP6(sK5(X0,X1),sK4(X0,X1),X1,X0) | k2_funct_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f387,plain,(
% 0.21/0.49    spl7_35 | ~spl7_12 | ~spl7_24 | ~spl7_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f376,f293,f243,f140,f384])).
% 0.21/0.49  fof(f376,plain,(
% 0.21/0.49    sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2) | (~spl7_12 | ~spl7_24 | ~spl7_28)),
% 0.21/0.49    inference(subsumption_resolution,[],[f375,f245])).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK2,sK3),sK1) | sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,sK2) | (~spl7_12 | ~spl7_28)),
% 0.21/0.49    inference(superposition,[],[f360,f142])).
% 0.21/0.49  % (11475)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(sK4(sK2,sK3),k2_relat_1(X1)) | sP6(sK5(sK2,sK3),sK4(sK2,sK3),sK3,X1)) ) | ~spl7_28),
% 0.21/0.49    inference(superposition,[],[f63,f295])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sP6(k1_funct_1(X1,X2),X2,X1,X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,k2_relat_1(X0)) | k1_funct_1(X1,X2) != X3 | sP6(X3,X2,X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f356,plain,(
% 0.21/0.49    sK4(sK2,sK3) != k1_funct_1(sK2,sK5(sK2,sK3)) | sK5(sK2,sK3) != k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3))) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f355,plain,(
% 0.21/0.49    spl7_34 | ~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_12 | ~spl7_17 | ~spl7_20 | ~spl7_22 | spl7_28),
% 0.21/0.49    inference(avatar_split_clause,[],[f350,f293,f235,f208,f174,f140,f102,f82,f77,f72,f352])).
% 0.21/0.49  fof(f350,plain,(
% 0.21/0.49    sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_12 | ~spl7_17 | ~spl7_20 | ~spl7_22 | spl7_28)),
% 0.21/0.49    inference(subsumption_resolution,[],[f277,f294])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    sK5(sK2,sK3) != k1_funct_1(sK3,sK4(sK2,sK3)) | spl7_28),
% 0.21/0.49    inference(avatar_component_clause,[],[f293])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_12 | ~spl7_17 | ~spl7_20 | ~spl7_22)),
% 0.21/0.49    inference(subsumption_resolution,[],[f276,f104])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | sK3 = k2_funct_1(sK2) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_17 | ~spl7_20 | ~spl7_22)),
% 0.21/0.49    inference(subsumption_resolution,[],[f275,f176])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | sK1 != k1_relat_1(sK3) | sK3 = k2_funct_1(sK2) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_20 | ~spl7_22)),
% 0.21/0.49    inference(subsumption_resolution,[],[f273,f236])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | sK1 != k1_relat_1(sK3) | sK3 = k2_funct_1(sK2) | sK4(sK2,sK3) = k1_funct_1(sK2,sK5(sK2,sK3)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_20)),
% 0.21/0.49    inference(resolution,[],[f231,f74])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | sK5(sK2,X1) = k1_funct_1(X1,sK4(sK2,X1)) | k1_relat_1(X1) != sK1 | k2_funct_1(sK2) = X1 | sK4(sK2,X1) = k1_funct_1(sK2,sK5(sK2,X1))) ) | (~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_20)),
% 0.21/0.49    inference(resolution,[],[f223,f36])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ( ! [X3] : (~sP6(sK5(sK2,X3),sK4(sK2,X3),X3,sK2) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3)) | sK1 != k1_relat_1(X3) | k2_funct_1(sK2) = X3) ) | (~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f150,f209])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    ( ! [X3] : (sK1 != k1_relat_1(X3) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(sK2) | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3)) | ~sP6(sK5(sK2,X3),sK4(sK2,X3),X3,sK2) | k2_funct_1(sK2) = X3) ) | (~spl7_2 | ~spl7_3 | ~spl7_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f149,f79])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ( ! [X3] : (sK1 != k1_relat_1(X3) | ~v2_funct_1(sK2) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(sK2) | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3)) | ~sP6(sK5(sK2,X3),sK4(sK2,X3),X3,sK2) | k2_funct_1(sK2) = X3) ) | (~spl7_3 | ~spl7_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f146,f84])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ( ! [X3] : (sK1 != k1_relat_1(X3) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(sK2) | sK5(sK2,X3) = k1_funct_1(X3,sK4(sK2,X3)) | ~sP6(sK5(sK2,X3),sK4(sK2,X3),X3,sK2) | k2_funct_1(sK2) = X3) ) | ~spl7_12),
% 0.21/0.49    inference(superposition,[],[f41,f142])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | sK5(X0,X1) = k1_funct_1(X1,sK4(X0,X1)) | ~sP6(sK5(X0,X1),sK4(X0,X1),X1,X0) | k2_funct_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    spl7_33 | ~spl7_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f306,f239,f333])).
% 0.21/0.49  fof(f333,plain,(
% 0.21/0.49    spl7_33 <=> sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    sK5(sK2,sK3) = k1_funct_1(sK3,k1_funct_1(sK2,sK5(sK2,sK3))) | ~spl7_23),
% 0.21/0.49    inference(resolution,[],[f241,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X5] : (~r2_hidden(X5,sK0) | k1_funct_1(sK3,k1_funct_1(sK2,X5)) = X5) )),
% 0.21/0.49    inference(equality_resolution,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r2_hidden(X5,sK0) | k1_funct_1(sK2,X5) != X4 | k1_funct_1(sK3,X4) = X5) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    spl7_28 | ~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | ~spl7_22 | spl7_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f286,f239,f235,f208,f186,f174,f140,f102,f82,f77,f72,f293])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | ~spl7_22 | spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f270,f236])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_7 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f269,f104])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | sK3 = k2_funct_1(sK2) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_17 | ~spl7_19 | ~spl7_20 | spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f268,f176])).
% 0.21/0.49  fof(f268,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | sK1 != k1_relat_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_19 | ~spl7_20 | spl7_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f266,f240])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | r2_hidden(sK5(sK2,sK3),sK0) | sK5(sK2,sK3) = k1_funct_1(sK3,sK4(sK2,sK3)) | sK1 != k1_relat_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_19 | ~spl7_20)),
% 0.21/0.49    inference(resolution,[],[f232,f74])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK5(sK2,X0),sK0) | sK5(sK2,X0) = k1_funct_1(X0,sK4(sK2,X0)) | k1_relat_1(X0) != sK1 | k2_funct_1(sK2) = X0) ) | (~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_19 | ~spl7_20)),
% 0.21/0.49    inference(forward_demodulation,[],[f230,f188])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sK5(sK2,X0) = k1_funct_1(X0,sK4(sK2,X0)) | k1_relat_1(X0) != sK1 | k2_funct_1(sK2) = X0 | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))) ) | (~spl7_2 | ~spl7_3 | ~spl7_12 | ~spl7_20)),
% 0.21/0.49    inference(resolution,[],[f223,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sP6(X3,X2,X1,X0) | r2_hidden(X3,k1_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    spl7_27 | ~spl7_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f285,f243,f288])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    spl7_27 <=> sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    sK4(sK2,sK3) = k1_funct_1(sK2,k1_funct_1(sK3,sK4(sK2,sK3))) | ~spl7_24),
% 0.21/0.49    inference(resolution,[],[f245,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X4] : (~r2_hidden(X4,sK1) | k1_funct_1(sK2,k1_funct_1(sK3,X4)) = X4) )),
% 0.21/0.49    inference(equality_resolution,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X4,X5] : (~r2_hidden(X4,sK1) | k1_funct_1(sK3,X4) != X5 | k1_funct_1(sK2,X5) = X4) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    ~spl7_9 | spl7_22),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f254])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    $false | (~spl7_9 | spl7_22)),
% 0.21/0.49    inference(resolution,[],[f247,f114])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl7_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl7_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_22),
% 0.21/0.49    inference(resolution,[],[f237,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | spl7_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f235])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    ~spl7_22 | spl7_23 | spl7_24 | ~spl7_1 | spl7_7 | ~spl7_17 | ~spl7_19 | ~spl7_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f227,f212,f186,f174,f102,f72,f243,f239,f235])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    r2_hidden(sK4(sK2,sK3),sK1) | r2_hidden(sK5(sK2,sK3),sK0) | ~v1_relat_1(sK3) | (~spl7_1 | spl7_7 | ~spl7_17 | ~spl7_19 | ~spl7_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f226,f176])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    r2_hidden(sK4(sK2,sK3),sK1) | sK1 != k1_relat_1(sK3) | r2_hidden(sK5(sK2,sK3),sK0) | ~v1_relat_1(sK3) | (~spl7_1 | spl7_7 | ~spl7_19 | ~spl7_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f224,f104])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    sK3 = k2_funct_1(sK2) | r2_hidden(sK4(sK2,sK3),sK1) | sK1 != k1_relat_1(sK3) | r2_hidden(sK5(sK2,sK3),sK0) | ~v1_relat_1(sK3) | (~spl7_1 | ~spl7_19 | ~spl7_21)),
% 0.21/0.49    inference(resolution,[],[f221,f74])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(X0) | k2_funct_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),sK1) | k1_relat_1(X0) != sK1 | r2_hidden(sK5(sK2,X0),sK0) | ~v1_relat_1(X0)) ) | (~spl7_19 | ~spl7_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f219,f188])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ( ! [X0] : (k2_funct_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),sK1) | k1_relat_1(X0) != sK1 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))) ) | ~spl7_21),
% 0.21/0.49    inference(resolution,[],[f213,f35])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    ~spl7_11 | spl7_20),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f216])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    $false | (~spl7_11 | spl7_20)),
% 0.21/0.49    inference(resolution,[],[f215,f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl7_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_20),
% 0.21/0.49    inference(resolution,[],[f210,f44])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~v1_relat_1(sK2) | spl7_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f208])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ~spl7_20 | spl7_21 | ~spl7_2 | ~spl7_3 | ~spl7_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f148,f140,f82,f77,f212,f208])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ( ! [X2] : (r2_hidden(sK4(sK2,X2),sK1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(sK2) | ~sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2) | k2_funct_1(sK2) = X2) ) | (~spl7_2 | ~spl7_3 | ~spl7_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f147,f79])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ( ! [X2] : (r2_hidden(sK4(sK2,X2),sK1) | ~v2_funct_1(sK2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(sK2) | ~sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2) | k2_funct_1(sK2) = X2) ) | (~spl7_3 | ~spl7_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f145,f84])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    ( ! [X2] : (r2_hidden(sK4(sK2,X2),sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(sK2) | ~sP6(sK5(sK2,X2),sK4(sK2,X2),X2,sK2) | k2_funct_1(sK2) = X2) ) | ~spl7_12),
% 0.21/0.49    inference(superposition,[],[f40,f142])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_relat_1(X0) | ~sP6(sK5(X0,X1),sK4(X0,X1),X1,X0) | k2_funct_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    spl7_19 | ~spl7_15 | ~spl7_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f192,f180,f164,f186])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl7_15 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    spl7_18 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | (~spl7_15 | ~spl7_18)),
% 0.21/0.49    inference(superposition,[],[f182,f166])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl7_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f164])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f180])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    k1_relset_1(sK1,sK0,sK3) != k1_relat_1(sK3) | sK1 != k1_relset_1(sK1,sK0,sK3) | sK1 = k1_relat_1(sK3)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    spl7_18 | spl7_5 | ~spl7_8 | ~spl7_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f137,f122,f107,f92,f180])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl7_5 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl7_8 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | (spl7_5 | ~spl7_8 | ~spl7_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f136,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1) | ~spl7_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | (spl7_5 | ~spl7_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f133,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | spl7_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl7_11),
% 0.21/0.49    inference(resolution,[],[f124,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl7_16 | spl7_4 | ~spl7_6 | ~spl7_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f131,f112,f97,f87,f169])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    spl7_16 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl7_4 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl7_6 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK0,sK3) | (spl7_4 | ~spl7_6 | ~spl7_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK0) | ~spl7_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | (spl7_4 | ~spl7_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f127,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | spl7_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~spl7_9),
% 0.21/0.49    inference(resolution,[],[f114,f52])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    spl7_15 | ~spl7_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f135,f122,f164])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl7_11),
% 0.21/0.49    inference(resolution,[],[f124,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl7_14 | ~spl7_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f129,f112,f159])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl7_14 <=> k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) | ~spl7_9),
% 0.21/0.49    inference(resolution,[],[f114,f45])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl7_12 | ~spl7_10 | ~spl7_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f138,f122,f117,f140])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl7_10 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    sK1 = k2_relat_1(sK2) | (~spl7_10 | ~spl7_11)),
% 0.21/0.49    inference(forward_demodulation,[],[f134,f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl7_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f117])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl7_11),
% 0.21/0.49    inference(resolution,[],[f124,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl7_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f122])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl7_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f117])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl7_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f112])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl7_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f107])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ~spl7_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f102])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    sK3 != k2_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl7_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f97])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~spl7_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f92])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ~spl7_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f87])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl7_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f82])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl7_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f77])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    v2_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl7_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f72])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11474)------------------------------
% 0.21/0.49  % (11474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11474)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11474)Memory used [KB]: 10874
% 0.21/0.49  % (11474)Time elapsed: 0.074 s
% 0.21/0.49  % (11474)------------------------------
% 0.21/0.49  % (11474)------------------------------
% 0.21/0.49  % (11482)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  % (11470)Success in time 0.135 s
%------------------------------------------------------------------------------
