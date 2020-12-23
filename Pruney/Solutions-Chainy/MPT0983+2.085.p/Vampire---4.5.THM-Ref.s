%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 375 expanded)
%              Number of leaves         :   51 ( 161 expanded)
%              Depth                    :   14
%              Number of atoms          :  797 (1562 expanded)
%              Number of equality atoms :   90 ( 117 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f652,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f115,f120,f125,f130,f135,f140,f145,f150,f156,f172,f196,f210,f243,f271,f281,f302,f312,f333,f341,f368,f376,f383,f420,f425,f462,f651])).

fof(f651,plain,
    ( spl7_1
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | spl7_1
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(subsumption_resolution,[],[f648,f105])).

fof(f105,plain,
    ( ~ v2_funct_1(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f648,plain,
    ( v2_funct_1(sK2)
    | ~ spl7_33
    | ~ spl7_43 ),
    inference(resolution,[],[f484,f382])).

fof(f382,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f380])).

fof(f380,plain,
    ( spl7_33
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f484,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v2_funct_1(X0) )
    | ~ spl7_43 ),
    inference(superposition,[],[f451,f89])).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f451,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl7_43
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f462,plain,
    ( ~ spl7_37
    | ~ spl7_38
    | spl7_43
    | ~ spl7_23
    | ~ spl7_25
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f461,f305,f276,f240,f449,f422,f417])).

fof(f417,plain,
    ( spl7_37
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f422,plain,
    ( spl7_38
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f240,plain,
    ( spl7_23
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f276,plain,
    ( spl7_25
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f305,plain,
    ( spl7_28
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f461,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_23
    | ~ spl7_25
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f460,f307])).

fof(f307,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f305])).

fof(f460,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | v2_funct_1(sK3)
    | ~ spl7_23
    | ~ spl7_25
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f459,f307])).

fof(f459,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl7_23
    | ~ spl7_25
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f458,f307])).

fof(f458,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl7_23
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f315,f241])).

fof(f241,plain,
    ( v1_xboole_0(sK0)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f240])).

fof(f315,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | ~ spl7_25 ),
    inference(superposition,[],[f216,f278])).

fof(f278,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f276])).

fof(f216,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(resolution,[],[f73,f96])).

fof(f96,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k2_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1))
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK5(X0)))
            & r2_hidden(sK5(X0),k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f52,f54,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
     => k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4)
          & r2_hidden(X3,k2_relat_1(X0)) )
     => ( ! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK5(X0)))
        & r2_hidden(sK5(X0),k2_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ? [X3] :
              ( ! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4)
              & r2_hidden(X3,k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( ! [X1] :
              ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
              | ~ r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v2_funct_1(X0) )
        & ( v2_funct_1(X0)
          | ? [X1] :
              ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
              & r2_hidden(X1,k2_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

% (4807)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f31,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] :
            ~ ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
              & r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

fof(f425,plain,
    ( spl7_38
    | ~ spl7_12
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f392,f305,f169,f422])).

fof(f169,plain,
    ( spl7_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f392,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_28 ),
    inference(backward_demodulation,[],[f171,f307])).

fof(f171,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f169])).

fof(f420,plain,
    ( spl7_37
    | ~ spl7_6
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f391,f305,f127,f417])).

fof(f127,plain,
    ( spl7_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f391,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_6
    | ~ spl7_28 ),
    inference(backward_demodulation,[],[f129,f307])).

fof(f129,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f383,plain,
    ( spl7_33
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f377,f190,f380])).

fof(f190,plain,
    ( spl7_16
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f377,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_16 ),
    inference(resolution,[],[f191,f97])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f191,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f376,plain,
    ( spl7_29
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f375,f330,f142,f137,f132,f127,f122,f117,f103,f309])).

fof(f309,plain,
    ( spl7_29
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f117,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f122,plain,
    ( spl7_5
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f132,plain,
    ( spl7_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f137,plain,
    ( spl7_8
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f142,plain,
    ( spl7_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f330,plain,
    ( spl7_31
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f375,plain,
    ( k1_xboole_0 = sK0
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f374,f144])).

fof(f144,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f374,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f373,f139])).

fof(f139,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f373,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f372,f134])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f372,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f371,f129])).

fof(f371,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f370,f124])).

fof(f124,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f370,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl7_1
    | ~ spl7_4
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f369,f119])).

fof(f119,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f369,plain,
    ( k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl7_1
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f358,f105])).

fof(f358,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f347,f77])).

fof(f77,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f347,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl7_31 ),
    inference(superposition,[],[f71,f332])).

fof(f332,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f330])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f368,plain,
    ( k1_xboole_0 != sK0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f341,plain,
    ( ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | spl7_30 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_9
    | spl7_30 ),
    inference(subsumption_resolution,[],[f339,f144])).

fof(f339,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | spl7_30 ),
    inference(subsumption_resolution,[],[f338,f134])).

fof(f338,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl7_4
    | ~ spl7_6
    | spl7_30 ),
    inference(subsumption_resolution,[],[f337,f129])).

fof(f337,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl7_4
    | spl7_30 ),
    inference(subsumption_resolution,[],[f335,f119])).

fof(f335,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl7_30 ),
    inference(resolution,[],[f328,f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f328,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_30 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl7_30
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f333,plain,
    ( ~ spl7_30
    | spl7_31
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f323,f153,f330,f326])).

fof(f153,plain,
    ( spl7_11
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f323,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_11 ),
    inference(resolution,[],[f248,f155])).

fof(f155,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f248,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f78,f87])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f312,plain,
    ( spl7_28
    | ~ spl7_29
    | ~ spl7_12
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f303,f276,f169,f309,f305])).

fof(f303,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK3
    | ~ spl7_12
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f286,f171])).

fof(f286,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl7_25 ),
    inference(superposition,[],[f91,f278])).

fof(f91,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f302,plain,
    ( spl7_2
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f301,f276,f207,f169,f107])).

fof(f107,plain,
    ( spl7_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f207,plain,
    ( spl7_19
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f301,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f300,f171])).

fof(f300,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_19
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f285,f209])).

fof(f209,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f207])).

fof(f285,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_25 ),
    inference(superposition,[],[f98,f278])).

fof(f98,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

% (4795)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f281,plain,
    ( spl7_25
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f280,f268,f117,f276])).

fof(f268,plain,
    ( spl7_24
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f280,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl7_4
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f273,f119])).

fof(f273,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_24 ),
    inference(superposition,[],[f85,f270])).

fof(f270,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f268])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f271,plain,
    ( spl7_24
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f266,f153,f142,f137,f132,f127,f122,f117,f268])).

fof(f266,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f265,f129])).

fof(f265,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f264,f124])).

fof(f264,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl7_4
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f263,f119])).

fof(f263,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f262,f144])).

fof(f262,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f261,f139])).

fof(f261,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f260,f134])).

fof(f260,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f257,f155])).

fof(f257,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f80,f81])).

fof(f81,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f243,plain,
    ( ~ spl7_23
    | spl7_17 ),
    inference(avatar_split_clause,[],[f238,f193,f240])).

fof(f193,plain,
    ( spl7_17
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f238,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_17 ),
    inference(resolution,[],[f195,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f195,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f210,plain,
    ( spl7_19
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f203,f117,f207])).

fof(f203,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f92,f119])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f196,plain,
    ( spl7_16
    | ~ spl7_17
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f179,f132,f193,f190])).

fof(f179,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl7_7 ),
    inference(resolution,[],[f84,f134])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f172,plain,
    ( spl7_12
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f165,f117,f169])).

fof(f165,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f119])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f156,plain,
    ( spl7_11
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f151,f112,f153])).

fof(f112,plain,
    ( spl7_3
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f151,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f114,f81])).

fof(f114,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f150,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f94,f147])).

fof(f147,plain,
    ( spl7_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f94,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f145,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f61,f142])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f48,f47])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f140,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f62,f137])).

fof(f62,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f135,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f63,f132])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f130,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f64,f127])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f125,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f65,f122])).

fof(f65,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f120,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f66,f117])).

fof(f66,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f115,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f67,f112])).

fof(f67,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f110,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f68,f107,f103])).

fof(f68,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:24:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (4790)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (4814)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (4806)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (4801)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.50  % (4793)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (4798)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (4801)Refutation not found, incomplete strategy% (4801)------------------------------
% 0.20/0.50  % (4801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4809)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.51  % (4797)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (4785)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (4801)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4801)Memory used [KB]: 10746
% 0.20/0.51  % (4801)Time elapsed: 0.099 s
% 0.20/0.51  % (4801)------------------------------
% 0.20/0.51  % (4801)------------------------------
% 0.20/0.51  % (4786)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (4799)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (4787)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (4813)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (4788)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (4800)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (4791)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (4805)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (4810)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (4789)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (4806)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f652,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f110,f115,f120,f125,f130,f135,f140,f145,f150,f156,f172,f196,f210,f243,f271,f281,f302,f312,f333,f341,f368,f376,f383,f420,f425,f462,f651])).
% 0.20/0.53  fof(f651,plain,(
% 0.20/0.53    spl7_1 | ~spl7_33 | ~spl7_43),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f650])).
% 0.20/0.53  fof(f650,plain,(
% 0.20/0.53    $false | (spl7_1 | ~spl7_33 | ~spl7_43)),
% 0.20/0.53    inference(subsumption_resolution,[],[f648,f105])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    ~v2_funct_1(sK2) | spl7_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f103])).
% 0.20/0.53  fof(f103,plain,(
% 0.20/0.53    spl7_1 <=> v2_funct_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.53  fof(f648,plain,(
% 0.20/0.53    v2_funct_1(sK2) | (~spl7_33 | ~spl7_43)),
% 0.20/0.53    inference(resolution,[],[f484,f382])).
% 0.20/0.53  fof(f382,plain,(
% 0.20/0.53    v1_xboole_0(sK2) | ~spl7_33),
% 0.20/0.53    inference(avatar_component_clause,[],[f380])).
% 0.20/0.53  fof(f380,plain,(
% 0.20/0.53    spl7_33 <=> v1_xboole_0(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.20/0.53  fof(f484,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(X0) | v2_funct_1(X0)) ) | ~spl7_43),
% 0.20/0.53    inference(superposition,[],[f451,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.53  fof(f451,plain,(
% 0.20/0.53    v2_funct_1(k1_xboole_0) | ~spl7_43),
% 0.20/0.53    inference(avatar_component_clause,[],[f449])).
% 0.20/0.53  fof(f449,plain,(
% 0.20/0.53    spl7_43 <=> v2_funct_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.20/0.53  fof(f462,plain,(
% 0.20/0.53    ~spl7_37 | ~spl7_38 | spl7_43 | ~spl7_23 | ~spl7_25 | ~spl7_28),
% 0.20/0.53    inference(avatar_split_clause,[],[f461,f305,f276,f240,f449,f422,f417])).
% 0.20/0.53  fof(f417,plain,(
% 0.20/0.53    spl7_37 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.20/0.53  fof(f422,plain,(
% 0.20/0.53    spl7_38 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.20/0.53  fof(f240,plain,(
% 0.20/0.53    spl7_23 <=> v1_xboole_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.53  fof(f276,plain,(
% 0.20/0.53    spl7_25 <=> sK0 = k2_relat_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.20/0.53  fof(f305,plain,(
% 0.20/0.53    spl7_28 <=> k1_xboole_0 = sK3),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.20/0.53  fof(f461,plain,(
% 0.20/0.53    v2_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl7_23 | ~spl7_25 | ~spl7_28)),
% 0.20/0.53    inference(forward_demodulation,[],[f460,f307])).
% 0.20/0.53  fof(f307,plain,(
% 0.20/0.53    k1_xboole_0 = sK3 | ~spl7_28),
% 0.20/0.53    inference(avatar_component_clause,[],[f305])).
% 0.20/0.53  fof(f460,plain,(
% 0.20/0.53    ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | v2_funct_1(sK3) | (~spl7_23 | ~spl7_25 | ~spl7_28)),
% 0.20/0.53    inference(forward_demodulation,[],[f459,f307])).
% 0.20/0.53  fof(f459,plain,(
% 0.20/0.53    ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(sK3) | v2_funct_1(sK3) | (~spl7_23 | ~spl7_25 | ~spl7_28)),
% 0.20/0.53    inference(forward_demodulation,[],[f458,f307])).
% 0.20/0.53  fof(f458,plain,(
% 0.20/0.53    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | v2_funct_1(sK3) | (~spl7_23 | ~spl7_25)),
% 0.20/0.53    inference(subsumption_resolution,[],[f315,f241])).
% 0.20/0.53  fof(f241,plain,(
% 0.20/0.53    v1_xboole_0(sK0) | ~spl7_23),
% 0.20/0.53    inference(avatar_component_clause,[],[f240])).
% 0.20/0.53  fof(f315,plain,(
% 0.20/0.53    ~v1_xboole_0(sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | v2_funct_1(sK3) | ~spl7_25),
% 0.20/0.53    inference(superposition,[],[f216,f278])).
% 0.20/0.53  fof(f278,plain,(
% 0.20/0.53    sK0 = k2_relat_1(sK3) | ~spl7_25),
% 0.20/0.53    inference(avatar_component_clause,[],[f276])).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.20/0.53    inference(resolution,[],[f73,f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f58,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(rectify,[],[f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK5(X0),k2_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ! [X0] : (((! [X1] : (k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1)) | ~r2_hidden(X1,k2_relat_1(X0))) | ~v2_funct_1(X0)) & (v2_funct_1(X0) | (! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK5(X0))) & r2_hidden(sK5(X0),k2_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f52,f54,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) => k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(sK4(X0,X1)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ! [X0] : (? [X3] : (! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4) & r2_hidden(X3,k2_relat_1(X0))) => (! [X4] : k1_tarski(X4) != k10_relat_1(X0,k1_tarski(sK5(X0))) & r2_hidden(sK5(X0),k2_relat_1(X0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ! [X0] : (((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) | ~v2_funct_1(X0)) & (v2_funct_1(X0) | ? [X3] : (! [X4] : k10_relat_1(X0,k1_tarski(X3)) != k1_tarski(X4) & r2_hidden(X3,k2_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(rectify,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X0] : (((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) | ~v2_funct_1(X0)) & (v2_funct_1(X0) | ? [X1] : (! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f31])).
% 0.20/0.53  % (4807)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (! [X1] : ~(! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).
% 0.20/0.53  fof(f425,plain,(
% 0.20/0.53    spl7_38 | ~spl7_12 | ~spl7_28),
% 0.20/0.53    inference(avatar_split_clause,[],[f392,f305,f169,f422])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    spl7_12 <=> v1_relat_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.53  fof(f392,plain,(
% 0.20/0.53    v1_relat_1(k1_xboole_0) | (~spl7_12 | ~spl7_28)),
% 0.20/0.53    inference(backward_demodulation,[],[f171,f307])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~spl7_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f169])).
% 0.20/0.53  fof(f420,plain,(
% 0.20/0.53    spl7_37 | ~spl7_6 | ~spl7_28),
% 0.20/0.53    inference(avatar_split_clause,[],[f391,f305,f127,f417])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    spl7_6 <=> v1_funct_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.53  fof(f391,plain,(
% 0.20/0.53    v1_funct_1(k1_xboole_0) | (~spl7_6 | ~spl7_28)),
% 0.20/0.53    inference(backward_demodulation,[],[f129,f307])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    v1_funct_1(sK3) | ~spl7_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f127])).
% 0.20/0.53  fof(f383,plain,(
% 0.20/0.53    spl7_33 | ~spl7_16),
% 0.20/0.53    inference(avatar_split_clause,[],[f377,f190,f380])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    spl7_16 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.53  fof(f377,plain,(
% 0.20/0.53    v1_xboole_0(sK2) | ~spl7_16),
% 0.20/0.53    inference(resolution,[],[f191,f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f60])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl7_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f190])).
% 0.20/0.53  fof(f376,plain,(
% 0.20/0.53    spl7_29 | spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_31),
% 0.20/0.53    inference(avatar_split_clause,[],[f375,f330,f142,f137,f132,f127,f122,f117,f103,f309])).
% 0.20/0.53  fof(f309,plain,(
% 0.20/0.53    spl7_29 <=> k1_xboole_0 = sK0),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    spl7_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    spl7_5 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    spl7_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    spl7_8 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    spl7_9 <=> v1_funct_1(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.53  fof(f330,plain,(
% 0.20/0.53    spl7_31 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.20/0.53  fof(f375,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f374,f144])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    v1_funct_1(sK2) | ~spl7_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f142])).
% 0.20/0.53  fof(f374,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~v1_funct_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f373,f139])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    v1_funct_2(sK2,sK0,sK1) | ~spl7_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f137])).
% 0.20/0.53  fof(f373,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f372,f134])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f132])).
% 0.20/0.53  fof(f372,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f371,f129])).
% 0.20/0.53  fof(f371,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_5 | ~spl7_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f370,f124])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK1,sK0) | ~spl7_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f122])).
% 0.20/0.53  fof(f370,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl7_1 | ~spl7_4 | ~spl7_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f369,f119])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl7_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f117])).
% 0.20/0.53  fof(f369,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl7_1 | ~spl7_31)),
% 0.20/0.53    inference(subsumption_resolution,[],[f358,f105])).
% 0.20/0.53  fof(f358,plain,(
% 0.20/0.53    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl7_31),
% 0.20/0.53    inference(subsumption_resolution,[],[f347,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.53  fof(f347,plain,(
% 0.20/0.53    ~v2_funct_1(k6_relat_1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl7_31),
% 0.20/0.53    inference(superposition,[],[f71,f332])).
% 0.20/0.53  fof(f332,plain,(
% 0.20/0.53    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl7_31),
% 0.20/0.53    inference(avatar_component_clause,[],[f330])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f20])).
% 0.20/0.53  fof(f20,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 0.20/0.53  fof(f368,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | v1_xboole_0(sK0) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.53  fof(f341,plain,(
% 0.20/0.53    ~spl7_4 | ~spl7_6 | ~spl7_7 | ~spl7_9 | spl7_30),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f340])).
% 0.20/0.53  fof(f340,plain,(
% 0.20/0.53    $false | (~spl7_4 | ~spl7_6 | ~spl7_7 | ~spl7_9 | spl7_30)),
% 0.20/0.53    inference(subsumption_resolution,[],[f339,f144])).
% 0.20/0.53  fof(f339,plain,(
% 0.20/0.53    ~v1_funct_1(sK2) | (~spl7_4 | ~spl7_6 | ~spl7_7 | spl7_30)),
% 0.20/0.53    inference(subsumption_resolution,[],[f338,f134])).
% 0.20/0.53  fof(f338,plain,(
% 0.20/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl7_4 | ~spl7_6 | spl7_30)),
% 0.20/0.53    inference(subsumption_resolution,[],[f337,f129])).
% 0.20/0.53  fof(f337,plain,(
% 0.20/0.53    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl7_4 | spl7_30)),
% 0.20/0.53    inference(subsumption_resolution,[],[f335,f119])).
% 0.20/0.53  fof(f335,plain,(
% 0.20/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl7_30),
% 0.20/0.53    inference(resolution,[],[f328,f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.20/0.53    inference(flattening,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.20/0.53    inference(ennf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.20/0.53  fof(f328,plain,(
% 0.20/0.53    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl7_30),
% 0.20/0.53    inference(avatar_component_clause,[],[f326])).
% 0.20/0.53  fof(f326,plain,(
% 0.20/0.53    spl7_30 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.20/0.53  fof(f333,plain,(
% 0.20/0.53    ~spl7_30 | spl7_31 | ~spl7_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f323,f153,f330,f326])).
% 0.20/0.53  fof(f153,plain,(
% 0.20/0.53    spl7_11 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.53  fof(f323,plain,(
% 0.20/0.53    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_11),
% 0.20/0.53    inference(resolution,[],[f248,f155])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl7_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f153])).
% 0.20/0.53  fof(f248,plain,(
% 0.20/0.53    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.20/0.53    inference(resolution,[],[f78,f87])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,axiom,(
% 0.20/0.53    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.20/0.53  fof(f312,plain,(
% 0.20/0.53    spl7_28 | ~spl7_29 | ~spl7_12 | ~spl7_25),
% 0.20/0.53    inference(avatar_split_clause,[],[f303,f276,f169,f309,f305])).
% 0.20/0.53  fof(f303,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | k1_xboole_0 = sK3 | (~spl7_12 | ~spl7_25)),
% 0.20/0.53    inference(subsumption_resolution,[],[f286,f171])).
% 0.20/0.53  fof(f286,plain,(
% 0.20/0.53    k1_xboole_0 != sK0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl7_25),
% 0.20/0.53    inference(superposition,[],[f91,f278])).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(flattening,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.53  fof(f302,plain,(
% 0.20/0.53    spl7_2 | ~spl7_12 | ~spl7_19 | ~spl7_25),
% 0.20/0.53    inference(avatar_split_clause,[],[f301,f276,f207,f169,f107])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl7_2 <=> v2_funct_2(sK3,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.53  fof(f207,plain,(
% 0.20/0.53    spl7_19 <=> v5_relat_1(sK3,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.20/0.53  fof(f301,plain,(
% 0.20/0.53    v2_funct_2(sK3,sK0) | (~spl7_12 | ~spl7_19 | ~spl7_25)),
% 0.20/0.53    inference(subsumption_resolution,[],[f300,f171])).
% 0.20/0.53  fof(f300,plain,(
% 0.20/0.53    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | (~spl7_19 | ~spl7_25)),
% 0.20/0.53    inference(subsumption_resolution,[],[f285,f209])).
% 0.20/0.53  fof(f209,plain,(
% 0.20/0.53    v5_relat_1(sK3,sK0) | ~spl7_19),
% 0.20/0.53    inference(avatar_component_clause,[],[f207])).
% 0.20/0.53  fof(f285,plain,(
% 0.20/0.53    ~v5_relat_1(sK3,sK0) | v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl7_25),
% 0.20/0.53    inference(superposition,[],[f98,f278])).
% 0.20/0.53  fof(f98,plain,(
% 0.20/0.53    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f50])).
% 0.20/0.53  % (4795)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 0.20/0.53  fof(f281,plain,(
% 0.20/0.53    spl7_25 | ~spl7_4 | ~spl7_24),
% 0.20/0.53    inference(avatar_split_clause,[],[f280,f268,f117,f276])).
% 0.20/0.53  fof(f268,plain,(
% 0.20/0.53    spl7_24 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.20/0.53  fof(f280,plain,(
% 0.20/0.53    sK0 = k2_relat_1(sK3) | (~spl7_4 | ~spl7_24)),
% 0.20/0.53    inference(subsumption_resolution,[],[f273,f119])).
% 0.20/0.53  fof(f273,plain,(
% 0.20/0.53    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl7_24),
% 0.20/0.53    inference(superposition,[],[f85,f270])).
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl7_24),
% 0.20/0.53    inference(avatar_component_clause,[],[f268])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.53  fof(f271,plain,(
% 0.20/0.53    spl7_24 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f266,f153,f142,f137,f132,f127,f122,f117,f268])).
% 0.20/0.53  fof(f266,plain,(
% 0.20/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f265,f129])).
% 0.20/0.53  fof(f265,plain,(
% 0.20/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl7_4 | ~spl7_5 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f264,f124])).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl7_4 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f263,f119])).
% 0.20/0.53  fof(f263,plain,(
% 0.20/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f262,f144])).
% 0.20/0.53  fof(f262,plain,(
% 0.20/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl7_7 | ~spl7_8 | ~spl7_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f261,f139])).
% 0.20/0.53  fof(f261,plain,(
% 0.20/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl7_7 | ~spl7_11)),
% 0.20/0.53    inference(subsumption_resolution,[],[f260,f134])).
% 0.20/0.53  fof(f260,plain,(
% 0.20/0.53    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl7_11),
% 0.20/0.53    inference(resolution,[],[f257,f155])).
% 0.20/0.53  fof(f257,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(forward_demodulation,[],[f80,f81])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,axiom,(
% 0.20/0.53    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 0.20/0.53  fof(f243,plain,(
% 0.20/0.53    ~spl7_23 | spl7_17),
% 0.20/0.53    inference(avatar_split_clause,[],[f238,f193,f240])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    spl7_17 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.20/0.53  fof(f238,plain,(
% 0.20/0.53    ~v1_xboole_0(sK0) | spl7_17),
% 0.20/0.53    inference(resolution,[],[f195,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl7_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f193])).
% 0.20/0.53  fof(f210,plain,(
% 0.20/0.53    spl7_19 | ~spl7_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f203,f117,f207])).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    v5_relat_1(sK3,sK0) | ~spl7_4),
% 0.20/0.53    inference(resolution,[],[f92,f119])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    spl7_16 | ~spl7_17 | ~spl7_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f179,f132,f193,f190])).
% 0.20/0.53  fof(f179,plain,(
% 0.20/0.53    ( ! [X1] : (~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK2)) ) | ~spl7_7),
% 0.20/0.53    inference(resolution,[],[f84,f134])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.53  fof(f172,plain,(
% 0.20/0.53    spl7_12 | ~spl7_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f165,f117,f169])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~spl7_4),
% 0.20/0.53    inference(resolution,[],[f86,f119])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    spl7_11 | ~spl7_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f151,f112,f153])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    spl7_3 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.53  fof(f151,plain,(
% 0.20/0.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl7_3),
% 0.20/0.53    inference(backward_demodulation,[],[f114,f81])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl7_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f112])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    spl7_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f94,f147])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    spl7_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    spl7_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f61,f142])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    v1_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f48,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.53    inference(ennf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f21])).
% 0.20/0.53  fof(f21,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    spl7_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f62,f137])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    spl7_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f63,f132])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    spl7_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f64,f127])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f125,plain,(
% 0.20/0.53    spl7_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f65,f122])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f120,plain,(
% 0.20/0.53    spl7_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f66,f117])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    spl7_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f67,f112])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    ~spl7_1 | ~spl7_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f68,f107,f103])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (4806)------------------------------
% 0.20/0.53  % (4806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (4806)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (4806)Memory used [KB]: 6780
% 0.20/0.53  % (4806)Time elapsed: 0.122 s
% 0.20/0.53  % (4806)------------------------------
% 0.20/0.53  % (4806)------------------------------
% 0.20/0.53  % (4808)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (4812)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (4792)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (4784)Success in time 0.181 s
%------------------------------------------------------------------------------
