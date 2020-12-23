%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 207 expanded)
%              Number of leaves         :   22 (  84 expanded)
%              Depth                    :    7
%              Number of atoms          :  416 ( 816 expanded)
%              Number of equality atoms :   90 ( 220 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f60,f64,f68,f80,f84,f95,f112,f120,f130,f143,f147,f175,f193,f220,f231])).

fof(f231,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_15
    | spl6_29 ),
    inference(avatar_contradiction_clause,[],[f230])).

fof(f230,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_15
    | spl6_29 ),
    inference(subsumption_resolution,[],[f229,f111])).

fof(f111,plain,
    ( r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_15
  <=> r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f229,plain,
    ( ~ r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_10
    | spl6_29 ),
    inference(subsumption_resolution,[],[f228,f51])).

fof(f51,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl6_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f228,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl6_4
    | ~ spl6_10
    | spl6_29 ),
    inference(subsumption_resolution,[],[f226,f55])).

fof(f55,plain,
    ( v1_funct_1(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl6_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f226,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl6_10
    | spl6_29 ),
    inference(resolution,[],[f219,f79])).

% (10698)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f79,plain,
    ( ! [X2,X0] :
        ( r2_hidden(sK3(X0,X2),k1_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X2,k2_relat_1(X0)) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_10
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f219,plain,
    ( ~ r2_hidden(sK3(sK0,sK5(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl6_29
  <=> r2_hidden(sK3(sK0,sK5(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f220,plain,
    ( ~ spl6_29
    | ~ spl6_18
    | spl6_21
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f201,f191,f145,f128,f218])).

fof(f128,plain,
    ( spl6_18
  <=> sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK3(sK0,sK5(k2_relat_1(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f145,plain,
    ( spl6_21
  <=> sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f191,plain,
    ( spl6_27
  <=> ! [X0] :
        ( k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f201,plain,
    ( ~ r2_hidden(sK3(sK0,sK5(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ spl6_18
    | spl6_21
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f198,f146])).

fof(f146,plain,
    ( sK5(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f145])).

fof(f198,plain,
    ( sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1))
    | ~ r2_hidden(sK3(sK0,sK5(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))
    | ~ spl6_18
    | ~ spl6_27 ),
    inference(superposition,[],[f192,f129])).

fof(f129,plain,
    ( sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK3(sK0,sK5(k2_relat_1(sK0),sK1)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f128])).

fof(f192,plain,
    ( ! [X0] :
        ( k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( spl6_27
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f184,f173,f62,f46,f42,f191])).

fof(f42,plain,
    ( spl6_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f46,plain,
    ( spl6_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f62,plain,
    ( spl6_6
  <=> sK0 = k5_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f173,plain,
    ( spl6_25
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | k1_funct_1(k5_relat_1(sK0,X2),X3) = k1_funct_1(X2,k1_funct_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f184,plain,
    ( ! [X0] :
        ( k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0))
        | ~ r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_25 ),
    inference(forward_demodulation,[],[f183,f63])).

fof(f63,plain,
    ( sK0 = k5_relat_1(sK0,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(k5_relat_1(sK0,sK1),X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f181,f43])).

fof(f43,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK0))
        | k1_funct_1(k5_relat_1(sK0,sK1),X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) )
    | ~ spl6_2
    | ~ spl6_25 ),
    inference(resolution,[],[f174,f47])).

fof(f47,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f174,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | k1_funct_1(k5_relat_1(sK0,X2),X3) = k1_funct_1(X2,k1_funct_1(sK0,X3)) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f173])).

fof(f175,plain,
    ( spl6_25
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f157,f141,f54,f50,f173])).

fof(f141,plain,
    ( spl6_20
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f157,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | k1_funct_1(k5_relat_1(sK0,X2),X3) = k1_funct_1(X2,k1_funct_1(sK0,X3)) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f154,f51])).

fof(f154,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | k1_funct_1(k5_relat_1(sK0,X2),X3) = k1_funct_1(X2,k1_funct_1(sK0,X3)) )
    | ~ spl6_4
    | ~ spl6_20 ),
    inference(resolution,[],[f142,f55])).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f141])).

fof(f147,plain,
    ( ~ spl6_21
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | spl6_7
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f134,f118,f66,f58,f46,f42,f145])).

fof(f58,plain,
    ( spl6_5
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f66,plain,
    ( spl6_7
  <=> sK1 = k6_relat_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f118,plain,
    ( spl6_17
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | sK5(k1_relat_1(X1),X1) != k1_funct_1(X1,sK5(k1_relat_1(X1),X1))
        | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f134,plain,
    ( sK5(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | spl6_7
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f133,f67])).

fof(f67,plain,
    ( sK1 != k6_relat_1(k2_relat_1(sK0))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f133,plain,
    ( sK5(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1))
    | sK1 = k6_relat_1(k2_relat_1(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f132,f43])).

fof(f132,plain,
    ( sK5(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1))
    | ~ v1_relat_1(sK1)
    | sK1 = k6_relat_1(k2_relat_1(sK0))
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f131,f47])).

fof(f131,plain,
    ( sK5(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_relat_1(k2_relat_1(sK0))
    | ~ spl6_5
    | ~ spl6_17 ),
    inference(superposition,[],[f119,f59])).

fof(f59,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f119,plain,
    ( ! [X1] :
        ( sK5(k1_relat_1(X1),X1) != k1_funct_1(X1,sK5(k1_relat_1(X1),X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k6_relat_1(k1_relat_1(X1)) = X1 )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f143,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f31,f141])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f130,plain,
    ( spl6_18
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f123,f110,f82,f54,f50,f128])).

fof(f82,plain,
    ( spl6_11
  <=> ! [X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK3(X0,X2)) = X2
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f123,plain,
    ( sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK3(sK0,sK5(k2_relat_1(sK0),sK1)))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f122,plain,
    ( sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK3(sK0,sK5(k2_relat_1(sK0),sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f121,f55])).

fof(f121,plain,
    ( ~ v1_funct_1(sK0)
    | sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK3(sK0,sK5(k2_relat_1(sK0),sK1)))
    | ~ v1_relat_1(sK0)
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(resolution,[],[f111,f83])).

fof(f83,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | k1_funct_1(X0,sK3(X0,X2)) = X2
        | ~ v1_relat_1(X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f120,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f38,f118])).

fof(f38,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | sK5(k1_relat_1(X1),X1) != k1_funct_1(X1,sK5(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | sK5(X0,X1) != k1_funct_1(X1,sK5(X0,X1))
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).

fof(f112,plain,
    ( spl6_15
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | spl6_7
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f108,f93,f66,f58,f46,f42,f110])).

fof(f93,plain,
    ( spl6_13
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | r2_hidden(sK5(k1_relat_1(X1),X1),k1_relat_1(X1))
        | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f108,plain,
    ( r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | spl6_7
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f107,f67])).

fof(f107,plain,
    ( r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | sK1 = k6_relat_1(k2_relat_1(sK0))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f106,f43])).

fof(f106,plain,
    ( r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | sK1 = k6_relat_1(k2_relat_1(sK0))
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f105,f47])).

fof(f105,plain,
    ( r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k6_relat_1(k2_relat_1(sK0))
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(superposition,[],[f94,f59])).

fof(f94,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(k1_relat_1(X1),X1),k1_relat_1(X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k6_relat_1(k1_relat_1(X1)) = X1 )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f39,f93])).

fof(f39,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK5(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != X0
      | r2_hidden(sK5(X0,X1),X0)
      | k6_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f84,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f34,f82])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f80,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f35,f78])).

fof(f35,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK3(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f40,f66])).

fof(f40,plain,(
    sK1 != k6_relat_1(k2_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f18,f16])).

fof(f16,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

% (10691)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f18,plain,(
    sK1 != k6_relat_1(k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f17,f62])).

fof(f17,plain,(
    sK0 = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f60,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f16,f58])).

fof(f56,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f20,f54])).

fof(f20,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f19,f50])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f15,f46])).

fof(f15,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f44,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f14,f42])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:22:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (10696)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (10708)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (10700)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (10709)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (10700)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (10693)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (10702)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (10701)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f44,f48,f52,f56,f60,f64,f68,f80,f84,f95,f112,f120,f130,f143,f147,f175,f193,f220,f231])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ~spl6_3 | ~spl6_4 | ~spl6_10 | ~spl6_15 | spl6_29),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f230])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    $false | (~spl6_3 | ~spl6_4 | ~spl6_10 | ~spl6_15 | spl6_29)),
% 0.21/0.49    inference(subsumption_resolution,[],[f229,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | ~spl6_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl6_15 <=> r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    ~r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | (~spl6_3 | ~spl6_4 | ~spl6_10 | spl6_29)),
% 0.21/0.49    inference(subsumption_resolution,[],[f228,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    v1_relat_1(sK0) | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl6_3 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ~v1_relat_1(sK0) | ~r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | (~spl6_4 | ~spl6_10 | spl6_29)),
% 0.21/0.49    inference(subsumption_resolution,[],[f226,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    v1_funct_1(sK0) | ~spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl6_4 <=> v1_funct_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | (~spl6_10 | spl6_29)),
% 0.21/0.49    inference(resolution,[],[f219,f79])).
% 0.21/0.49  % (10698)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) ) | ~spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl6_10 <=> ! [X0,X2] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    ~r2_hidden(sK3(sK0,sK5(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) | spl6_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f218])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl6_29 <=> r2_hidden(sK3(sK0,sK5(k2_relat_1(sK0),sK1)),k1_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~spl6_29 | ~spl6_18 | spl6_21 | ~spl6_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f201,f191,f145,f128,f218])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl6_18 <=> sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK3(sK0,sK5(k2_relat_1(sK0),sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    spl6_21 <=> sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl6_27 <=> ! [X0] : (k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) | ~r2_hidden(X0,k1_relat_1(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ~r2_hidden(sK3(sK0,sK5(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) | (~spl6_18 | spl6_21 | ~spl6_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f198,f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    sK5(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1)) | spl6_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f145])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1)) | ~r2_hidden(sK3(sK0,sK5(k2_relat_1(sK0),sK1)),k1_relat_1(sK0)) | (~spl6_18 | ~spl6_27)),
% 0.21/0.49    inference(superposition,[],[f192,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK3(sK0,sK5(k2_relat_1(sK0),sK1))) | ~spl6_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f128])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ( ! [X0] : (k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) | ~r2_hidden(X0,k1_relat_1(sK0))) ) | ~spl6_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f191])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    spl6_27 | ~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_25),
% 0.21/0.49    inference(avatar_split_clause,[],[f184,f173,f62,f46,f42,f191])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl6_1 <=> v1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl6_2 <=> v1_funct_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl6_6 <=> sK0 = k5_relat_1(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    spl6_25 <=> ! [X3,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X3,k1_relat_1(sK0)) | k1_funct_1(k5_relat_1(sK0,X2),X3) = k1_funct_1(X2,k1_funct_1(sK0,X3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    ( ! [X0] : (k1_funct_1(sK0,X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0)) | ~r2_hidden(X0,k1_relat_1(sK0))) ) | (~spl6_1 | ~spl6_2 | ~spl6_6 | ~spl6_25)),
% 0.21/0.49    inference(forward_demodulation,[],[f183,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    sK0 = k5_relat_1(sK0,sK1) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(k5_relat_1(sK0,sK1),X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0))) ) | (~spl6_1 | ~spl6_2 | ~spl6_25)),
% 0.21/0.49    inference(subsumption_resolution,[],[f181,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v1_relat_1(sK1) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f42])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK0)) | k1_funct_1(k5_relat_1(sK0,sK1),X0) = k1_funct_1(sK1,k1_funct_1(sK0,X0))) ) | (~spl6_2 | ~spl6_25)),
% 0.21/0.49    inference(resolution,[],[f174,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    v1_funct_1(sK1) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f46])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(sK0)) | k1_funct_1(k5_relat_1(sK0,X2),X3) = k1_funct_1(X2,k1_funct_1(sK0,X3))) ) | ~spl6_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f173])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl6_25 | ~spl6_3 | ~spl6_4 | ~spl6_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f157,f141,f54,f50,f173])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    spl6_20 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X3,k1_relat_1(sK0)) | k1_funct_1(k5_relat_1(sK0,X2),X3) = k1_funct_1(X2,k1_funct_1(sK0,X3))) ) | (~spl6_3 | ~spl6_4 | ~spl6_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f154,f51])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~v1_relat_1(sK0) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X3,k1_relat_1(sK0)) | k1_funct_1(k5_relat_1(sK0,X2),X3) = k1_funct_1(X2,k1_funct_1(sK0,X3))) ) | (~spl6_4 | ~spl6_20)),
% 0.21/0.49    inference(resolution,[],[f142,f55])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) ) | ~spl6_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f141])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~spl6_21 | ~spl6_1 | ~spl6_2 | ~spl6_5 | spl6_7 | ~spl6_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f134,f118,f66,f58,f46,f42,f145])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl6_5 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl6_7 <=> sK1 = k6_relat_1(k2_relat_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    spl6_17 <=> ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | sK5(k1_relat_1(X1),X1) != k1_funct_1(X1,sK5(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    sK5(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1)) | (~spl6_1 | ~spl6_2 | ~spl6_5 | spl6_7 | ~spl6_17)),
% 0.21/0.49    inference(subsumption_resolution,[],[f133,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    sK1 != k6_relat_1(k2_relat_1(sK0)) | spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    sK5(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1)) | sK1 = k6_relat_1(k2_relat_1(sK0)) | (~spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_17)),
% 0.21/0.49    inference(subsumption_resolution,[],[f132,f43])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    sK5(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1)) | ~v1_relat_1(sK1) | sK1 = k6_relat_1(k2_relat_1(sK0)) | (~spl6_2 | ~spl6_5 | ~spl6_17)),
% 0.21/0.49    inference(subsumption_resolution,[],[f131,f47])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    sK5(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK5(k2_relat_1(sK0),sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_relat_1(k2_relat_1(sK0)) | (~spl6_5 | ~spl6_17)),
% 0.21/0.49    inference(superposition,[],[f119,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f58])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    ( ! [X1] : (sK5(k1_relat_1(X1),X1) != k1_funct_1(X1,sK5(k1_relat_1(X1),X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) ) | ~spl6_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f118])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl6_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f141])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl6_18 | ~spl6_3 | ~spl6_4 | ~spl6_11 | ~spl6_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f123,f110,f82,f54,f50,f128])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl6_11 <=> ! [X0,X2] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK3(sK0,sK5(k2_relat_1(sK0),sK1))) | (~spl6_3 | ~spl6_4 | ~spl6_11 | ~spl6_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f122,f51])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK3(sK0,sK5(k2_relat_1(sK0),sK1))) | ~v1_relat_1(sK0) | (~spl6_4 | ~spl6_11 | ~spl6_15)),
% 0.21/0.49    inference(subsumption_resolution,[],[f121,f55])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ~v1_funct_1(sK0) | sK5(k2_relat_1(sK0),sK1) = k1_funct_1(sK0,sK3(sK0,sK5(k2_relat_1(sK0),sK1))) | ~v1_relat_1(sK0) | (~spl6_11 | ~spl6_15)),
% 0.21/0.49    inference(resolution,[],[f111,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~v1_relat_1(X0)) ) | ~spl6_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl6_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f38,f118])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | sK5(k1_relat_1(X1),X1) != k1_funct_1(X1,sK5(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.49    inference(equality_resolution,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | sK5(X0,X1) != k1_funct_1(X1,sK5(X0,X1)) | k6_relat_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl6_15 | ~spl6_1 | ~spl6_2 | ~spl6_5 | spl6_7 | ~spl6_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f108,f93,f66,f58,f46,f42,f110])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl6_13 <=> ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK5(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | (~spl6_1 | ~spl6_2 | ~spl6_5 | spl6_7 | ~spl6_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f107,f67])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | sK1 = k6_relat_1(k2_relat_1(sK0)) | (~spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f106,f43])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | ~v1_relat_1(sK1) | sK1 = k6_relat_1(k2_relat_1(sK0)) | (~spl6_2 | ~spl6_5 | ~spl6_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f105,f47])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    r2_hidden(sK5(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | sK1 = k6_relat_1(k2_relat_1(sK0)) | (~spl6_5 | ~spl6_13)),
% 0.21/0.49    inference(superposition,[],[f94,f59])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X1] : (r2_hidden(sK5(k1_relat_1(X1),X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k6_relat_1(k1_relat_1(X1)) = X1) ) | ~spl6_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl6_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f39,f93])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r2_hidden(sK5(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1) )),
% 0.21/0.49    inference(equality_resolution,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != X0 | r2_hidden(sK5(X0,X1),X0) | k6_relat_1(X0) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl6_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f34,f82])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK3(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f35,f78])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK3(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~spl6_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f40,f66])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    sK1 != k6_relat_1(k2_relat_1(sK0))),
% 0.21/0.49    inference(backward_demodulation,[],[f18,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).
% 0.21/0.49  % (10691)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    sK1 != k6_relat_1(k1_relat_1(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f17,f62])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    sK0 = k5_relat_1(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f58])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f54])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f50])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f15,f46])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f42])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10700)------------------------------
% 0.21/0.49  % (10700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10700)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10700)Memory used [KB]: 10746
% 0.21/0.49  % (10700)Time elapsed: 0.072 s
% 0.21/0.49  % (10700)------------------------------
% 0.21/0.49  % (10700)------------------------------
% 0.21/0.49  % (10702)Refutation not found, incomplete strategy% (10702)------------------------------
% 0.21/0.49  % (10702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10705)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (10702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (10702)Memory used [KB]: 10746
% 0.21/0.49  % (10702)Time elapsed: 0.081 s
% 0.21/0.49  % (10702)------------------------------
% 0.21/0.49  % (10702)------------------------------
% 0.21/0.49  % (10690)Success in time 0.132 s
%------------------------------------------------------------------------------
