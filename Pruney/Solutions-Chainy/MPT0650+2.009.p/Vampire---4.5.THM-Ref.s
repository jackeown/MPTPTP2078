%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 333 expanded)
%              Number of leaves         :   35 ( 140 expanded)
%              Depth                    :   13
%              Number of atoms          :  546 ( 992 expanded)
%              Number of equality atoms :  113 ( 221 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (20287)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f1605,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f99,f108,f113,f120,f126,f143,f152,f167,f188,f193,f200,f214,f222,f418,f578,f706,f707,f708,f1583,f1604])).

fof(f1604,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | spl5_114 ),
    inference(avatar_contradiction_clause,[],[f1603])).

fof(f1603,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | spl5_114 ),
    inference(subsumption_resolution,[],[f1602,f66])).

fof(f66,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1602,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl5_4
    | spl5_114 ),
    inference(subsumption_resolution,[],[f1601,f98])).

fof(f98,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1601,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | spl5_114 ),
    inference(superposition,[],[f1582,f44])).

fof(f44,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f1582,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | spl5_114 ),
    inference(avatar_component_clause,[],[f1580])).

fof(f1580,plain,
    ( spl5_114
  <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f1583,plain,
    ( ~ spl5_114
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_14
    | spl5_16
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f1546,f575,f190,f180,f149,f140,f69,f64,f1580])).

fof(f69,plain,
    ( spl5_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f140,plain,
    ( spl5_10
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f149,plain,
    ( spl5_11
  <=> v1_funct_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f180,plain,
    ( spl5_14
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f190,plain,
    ( spl5_16
  <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f575,plain,
    ( spl5_48
  <=> k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f1546,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_14
    | spl5_16
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f1544,f181])).

fof(f181,plain,
    ( sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f1544,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))
    | ~ r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | spl5_16
    | ~ spl5_48 ),
    inference(superposition,[],[f192,f589])).

fof(f589,plain,
    ( ! [X2] :
        ( k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X2) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X2))
        | ~ r2_hidden(X2,k1_relat_1(k4_relat_1(sK1))) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f588,f142])).

fof(f142,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f140])).

fof(f588,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(k4_relat_1(sK1)))
        | ~ v1_relat_1(k4_relat_1(sK1))
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X2) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X2)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_11
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f581,f151])).

fof(f151,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f581,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(k4_relat_1(sK1)))
        | ~ v1_funct_1(k4_relat_1(sK1))
        | ~ v1_relat_1(k4_relat_1(sK1))
        | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X2) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X2)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_48 ),
    inference(superposition,[],[f83,f577])).

fof(f577,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f575])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1)))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1)) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f80,f66])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1)))
        | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f71,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).

fof(f71,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f192,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f190])).

fof(f708,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0) != sK4(sK1,sK0)
    | sK0 != k1_funct_1(sK1,sK4(sK1,sK0))
    | sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f707,plain,
    ( k2_funct_1(sK1) != k4_relat_1(sK1)
    | k1_funct_1(k4_relat_1(sK1),sK0) != sK4(sK1,sK0)
    | sK0 != k1_funct_1(sK1,sK4(sK1,sK0))
    | sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f706,plain,
    ( spl5_56
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_15
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f697,f197,f185,f123,f74,f69,f64,f703])).

fof(f703,plain,
    ( spl5_56
  <=> k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f74,plain,
    ( spl5_3
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f123,plain,
    ( spl5_9
  <=> k2_funct_1(sK1) = k4_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f185,plain,
    ( spl5_15
  <=> r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f197,plain,
    ( spl5_17
  <=> sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f697,plain,
    ( k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_15
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f195,f199])).

fof(f199,plain,
    ( sK0 = k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f197])).

% (20294)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f195,plain,
    ( sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9
    | ~ spl5_15 ),
    inference(resolution,[],[f187,f144])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f90,f125])).

fof(f125,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f89,f66])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f86,f71])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl5_3 ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f76,plain,
    ( v2_funct_1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f187,plain,
    ( r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f185])).

fof(f578,plain,
    ( spl5_48
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_19
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f566,f415,f211,f123,f110,f64,f575])).

fof(f110,plain,
    ( spl5_7
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f211,plain,
    ( spl5_19
  <=> k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f415,plain,
    ( spl5_36
  <=> k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f566,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_19
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f341,f417])).

fof(f417,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f415])).

fof(f341,plain,
    ( k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f340,f213])).

fof(f213,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f211])).

fof(f340,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) = k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f338,f66])).

fof(f338,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) = k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,
    ( ~ v1_relat_1(sK1)
    | k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) = k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(superposition,[],[f236,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f236,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(X2)))
        | k1_relat_1(k5_relat_1(k4_relat_1(sK1),k5_relat_1(sK1,k6_relat_1(X2)))) = k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,X2)) )
    | ~ spl5_1
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(superposition,[],[f233,f137])).

fof(f137,plain,
    ( ! [X0] : k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,X0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f135,f37])).

fof(f37,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f135,plain,
    ( ! [X0] :
        ( k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,X0)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl5_1 ),
    inference(superposition,[],[f78,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f78,plain,
    ( ! [X0] :
        ( k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f66,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f233,plain,
    ( ! [X0] :
        ( k1_relat_1(k5_relat_1(k4_relat_1(sK1),X0)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f114,f125])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) = k10_relat_1(k2_funct_1(sK1),k1_relat_1(X0)) )
    | ~ spl5_7 ),
    inference(resolution,[],[f112,f46])).

fof(f112,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f418,plain,
    ( spl5_36
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f274,f219,f123,f110,f415])).

fof(f219,plain,
    ( spl5_20
  <=> k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

% (20291)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f274,plain,
    ( k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_20 ),
    inference(superposition,[],[f238,f221])).

fof(f221,plain,
    ( k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f219])).

fof(f238,plain,
    ( ! [X0] : k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),X0)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f234,f37])).

fof(f234,plain,
    ( ! [X0] :
        ( k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),X0)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(superposition,[],[f233,f39])).

fof(f222,plain,
    ( spl5_20
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f217,f140,f117,f219])).

fof(f117,plain,
    ( spl5_8
  <=> k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f217,plain,
    ( k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1)))
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f121,f142])).

fof(f121,plain,
    ( k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1)))
    | ~ v1_relat_1(k4_relat_1(sK1))
    | ~ spl5_8 ),
    inference(superposition,[],[f43,f119])).

fof(f119,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f214,plain,
    ( spl5_19
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f203,f64,f211])).

fof(f203,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f201,f66])).

fof(f201,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl5_1 ),
    inference(superposition,[],[f137,f43])).

fof(f200,plain,
    ( spl5_17
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f169,f164,f197])).

fof(f164,plain,
    ( spl5_12
  <=> sP3(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f169,plain,
    ( sK0 = k1_funct_1(sK1,sK4(sK1,sK0))
    | ~ spl5_12 ),
    inference(resolution,[],[f166,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ sP3(X2,X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f166,plain,
    ( sP3(sK0,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f193,plain,
    ( ~ spl5_16
    | spl5_5
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f129,f123,f101,f190])).

fof(f101,plain,
    ( spl5_5
  <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f129,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)
    | spl5_5
    | ~ spl5_9 ),
    inference(superposition,[],[f103,f125])).

fof(f103,plain,
    ( sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f188,plain,
    ( spl5_15
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f168,f164,f185])).

fof(f168,plain,
    ( r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))
    | ~ spl5_12 ),
    inference(resolution,[],[f166,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( ~ sP3(X2,X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f167,plain,
    ( spl5_12
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f134,f96,f69,f64,f164])).

fof(f134,plain,
    ( sP3(sK0,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f84,f98])).

fof(f84,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK1))
        | sP3(X2,sK1) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f81,f66])).

fof(f81,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK1)
        | sP3(X2,sK1)
        | ~ r2_hidden(X2,k2_relat_1(sK1)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f71,f60])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP3(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f152,plain,
    ( spl5_11
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f132,f123,f69,f64,f149])).

fof(f132,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f131,f66])).

fof(f131,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f130,f71])).

fof(f130,plain,
    ( v1_funct_1(k4_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl5_9 ),
    inference(superposition,[],[f48,f125])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f143,plain,
    ( spl5_10
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f127,f123,f110,f140])).

fof(f127,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(superposition,[],[f112,f125])).

fof(f126,plain,
    ( spl5_9
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f94,f74,f69,f64,f123])).

fof(f94,plain,
    ( k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f93,f66])).

fof(f93,plain,
    ( ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f88,f71])).

fof(f88,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f76,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f120,plain,
    ( spl5_8
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f79,f64,f117])).

fof(f79,plain,
    ( k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f66,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f113,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f85,f69,f64,f110])).

fof(f85,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f82,f66])).

fof(f82,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_1(k2_funct_1(sK1))
    | ~ spl5_2 ),
    inference(resolution,[],[f71,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f108,plain,
    ( ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f32,f105,f101])).

fof(f105,plain,
    ( spl5_6
  <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f32,plain,
    ( sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))
    | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0
        | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0 )
      & r2_hidden(X0,k2_relat_1(X1))
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( r2_hidden(X0,k2_relat_1(X1))
            & v2_funct_1(X1) )
         => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
            & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).

fof(f99,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f36,f96])).

fof(f36,plain,(
    r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f35,f74])).

fof(f35,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:59:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (20280)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (20285)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (20292)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (20282)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (20277)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (20281)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (20290)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (20289)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (20280)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  % (20287)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f1605,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f67,f72,f77,f99,f108,f113,f120,f126,f143,f152,f167,f188,f193,f200,f214,f222,f418,f578,f706,f707,f708,f1583,f1604])).
% 0.21/0.51  fof(f1604,plain,(
% 0.21/0.51    ~spl5_1 | ~spl5_4 | spl5_114),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f1603])).
% 0.21/0.51  fof(f1603,plain,(
% 0.21/0.51    $false | (~spl5_1 | ~spl5_4 | spl5_114)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1602,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    v1_relat_1(sK1) | ~spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl5_1 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f1602,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | (~spl5_4 | spl5_114)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1601,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl5_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl5_4 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.51  fof(f1601,plain,(
% 0.21/0.51    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~v1_relat_1(sK1) | spl5_114),
% 0.21/0.51    inference(superposition,[],[f1582,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.51  fof(f1582,plain,(
% 0.21/0.51    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | spl5_114),
% 0.21/0.51    inference(avatar_component_clause,[],[f1580])).
% 0.21/0.51  fof(f1580,plain,(
% 0.21/0.51    spl5_114 <=> r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).
% 0.21/0.51  fof(f1583,plain,(
% 0.21/0.51    ~spl5_114 | ~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_11 | ~spl5_14 | spl5_16 | ~spl5_48),
% 0.21/0.51    inference(avatar_split_clause,[],[f1546,f575,f190,f180,f149,f140,f69,f64,f1580])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl5_2 <=> v1_funct_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl5_10 <=> v1_relat_1(k4_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    spl5_11 <=> v1_funct_1(k4_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    spl5_14 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    spl5_16 <=> sK0 = k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.51  fof(f575,plain,(
% 0.21/0.51    spl5_48 <=> k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 0.21/0.51  fof(f1546,plain,(
% 0.21/0.51    ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_11 | ~spl5_14 | spl5_16 | ~spl5_48)),
% 0.21/0.51    inference(subsumption_resolution,[],[f1544,f181])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~spl5_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f180])).
% 0.21/0.51  fof(f1544,plain,(
% 0.21/0.51    sK0 != k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0)) | ~r2_hidden(sK0,k1_relat_1(k4_relat_1(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_11 | spl5_16 | ~spl5_48)),
% 0.21/0.51    inference(superposition,[],[f192,f589])).
% 0.21/0.51  fof(f589,plain,(
% 0.21/0.51    ( ! [X2] : (k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X2) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X2)) | ~r2_hidden(X2,k1_relat_1(k4_relat_1(sK1)))) ) | (~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_11 | ~spl5_48)),
% 0.21/0.51    inference(subsumption_resolution,[],[f588,f142])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    v1_relat_1(k4_relat_1(sK1)) | ~spl5_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f140])).
% 0.21/0.51  fof(f588,plain,(
% 0.21/0.51    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k4_relat_1(sK1))) | ~v1_relat_1(k4_relat_1(sK1)) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X2) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X2))) ) | (~spl5_1 | ~spl5_2 | ~spl5_11 | ~spl5_48)),
% 0.21/0.51    inference(subsumption_resolution,[],[f581,f151])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    v1_funct_1(k4_relat_1(sK1)) | ~spl5_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f149])).
% 0.21/0.51  fof(f581,plain,(
% 0.21/0.51    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(k4_relat_1(sK1))) | ~v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(k4_relat_1(sK1)) | k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),X2) = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),X2))) ) | (~spl5_1 | ~spl5_2 | ~spl5_48)),
% 0.21/0.51    inference(superposition,[],[f83,f577])).
% 0.21/0.51  fof(f577,plain,(
% 0.21/0.51    k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) | ~spl5_48),
% 0.21/0.51    inference(avatar_component_clause,[],[f575])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1))) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f80,f66])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(X0,sK1))) | k1_funct_1(k5_relat_1(X0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(X0,X1))) ) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f71,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) => k1_funct_1(k5_relat_1(X2,X1),X0) = k1_funct_1(X1,k1_funct_1(X2,X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_funct_1)).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    v1_funct_1(sK1) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f69])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | spl5_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f190])).
% 0.21/0.51  fof(f708,plain,(
% 0.21/0.51    k1_funct_1(k4_relat_1(sK1),sK0) != sK4(sK1,sK0) | sK0 != k1_funct_1(sK1,sK4(sK1,sK0)) | sK0 = k1_funct_1(sK1,k1_funct_1(k4_relat_1(sK1),sK0))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f707,plain,(
% 0.21/0.51    k2_funct_1(sK1) != k4_relat_1(sK1) | k1_funct_1(k4_relat_1(sK1),sK0) != sK4(sK1,sK0) | sK0 != k1_funct_1(sK1,sK4(sK1,sK0)) | sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f706,plain,(
% 0.21/0.51    spl5_56 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_9 | ~spl5_15 | ~spl5_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f697,f197,f185,f123,f74,f69,f64,f703])).
% 0.21/0.51  fof(f703,plain,(
% 0.21/0.51    spl5_56 <=> k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    spl5_3 <=> v2_funct_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    spl5_9 <=> k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    spl5_15 <=> r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    spl5_17 <=> sK0 = k1_funct_1(sK1,sK4(sK1,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.51  fof(f697,plain,(
% 0.21/0.51    k1_funct_1(k4_relat_1(sK1),sK0) = sK4(sK1,sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_9 | ~spl5_15 | ~spl5_17)),
% 0.21/0.51    inference(forward_demodulation,[],[f195,f199])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) | ~spl5_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f197])).
% 0.21/0.51  % (20294)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    sK4(sK1,sK0) = k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,sK4(sK1,sK0))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_9 | ~spl5_15)),
% 0.21/0.51    inference(resolution,[],[f187,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k4_relat_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_9)),
% 0.21/0.51    inference(forward_demodulation,[],[f90,f125])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl5_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f123])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f89,f66])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl5_2 | ~spl5_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f71])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl5_3),
% 0.21/0.51    inference(resolution,[],[f76,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    v2_funct_1(sK1) | ~spl5_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f74])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | ~spl5_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f185])).
% 0.21/0.51  fof(f578,plain,(
% 0.21/0.51    spl5_48 | ~spl5_1 | ~spl5_7 | ~spl5_9 | ~spl5_19 | ~spl5_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f566,f415,f211,f123,f110,f64,f575])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl5_7 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    spl5_19 <=> k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.51  fof(f415,plain,(
% 0.21/0.51    spl5_36 <=> k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.51  fof(f566,plain,(
% 0.21/0.51    k1_relat_1(k4_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) | (~spl5_1 | ~spl5_7 | ~spl5_9 | ~spl5_19 | ~spl5_36)),
% 0.21/0.51    inference(forward_demodulation,[],[f341,f417])).
% 0.21/0.51  fof(f417,plain,(
% 0.21/0.51    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) | ~spl5_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f415])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) = k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) | (~spl5_1 | ~spl5_7 | ~spl5_9 | ~spl5_19)),
% 0.21/0.51    inference(forward_demodulation,[],[f340,f213])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~spl5_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f211])).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) = k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) | (~spl5_1 | ~spl5_7 | ~spl5_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f338,f66])).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) = k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) | (~spl5_1 | ~spl5_7 | ~spl5_9)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f337])).
% 0.21/0.51  fof(f337,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | k1_relat_1(k5_relat_1(k4_relat_1(sK1),sK1)) = k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,k2_relat_1(sK1))) | ~v1_relat_1(sK1) | (~spl5_1 | ~spl5_7 | ~spl5_9)),
% 0.21/0.51    inference(superposition,[],[f236,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ( ! [X2] : (~v1_relat_1(k5_relat_1(sK1,k6_relat_1(X2))) | k1_relat_1(k5_relat_1(k4_relat_1(sK1),k5_relat_1(sK1,k6_relat_1(X2)))) = k10_relat_1(k4_relat_1(sK1),k10_relat_1(sK1,X2))) ) | (~spl5_1 | ~spl5_7 | ~spl5_9)),
% 0.21/0.51    inference(superposition,[],[f233,f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,X0)) ) | ~spl5_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f135,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k5_relat_1(sK1,k6_relat_1(X0))) = k10_relat_1(sK1,X0) | ~v1_relat_1(k6_relat_1(X0))) ) | ~spl5_1),
% 0.21/0.51    inference(superposition,[],[f78,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k5_relat_1(sK1,X0)) = k10_relat_1(sK1,k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | ~spl5_1),
% 0.21/0.51    inference(resolution,[],[f66,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK1),X0)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl5_7 | ~spl5_9)),
% 0.21/0.51    inference(forward_demodulation,[],[f114,f125])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(k5_relat_1(k2_funct_1(sK1),X0)) = k10_relat_1(k2_funct_1(sK1),k1_relat_1(X0))) ) | ~spl5_7),
% 0.21/0.51    inference(resolution,[],[f112,f46])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK1)) | ~spl5_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f418,plain,(
% 0.21/0.51    spl5_36 | ~spl5_7 | ~spl5_9 | ~spl5_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f274,f219,f123,f110,f415])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    spl5_20 <=> k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.51  % (20291)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    k1_relat_1(k4_relat_1(sK1)) = k10_relat_1(k4_relat_1(sK1),k1_relat_1(sK1)) | (~spl5_7 | ~spl5_9 | ~spl5_20)),
% 0.21/0.51    inference(superposition,[],[f238,f221])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1))) | ~spl5_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f219])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),X0)) ) | (~spl5_7 | ~spl5_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f234,f37])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(k5_relat_1(k4_relat_1(sK1),k6_relat_1(X0))) = k10_relat_1(k4_relat_1(sK1),X0) | ~v1_relat_1(k6_relat_1(X0))) ) | (~spl5_7 | ~spl5_9)),
% 0.21/0.51    inference(superposition,[],[f233,f39])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    spl5_20 | ~spl5_8 | ~spl5_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f217,f140,f117,f219])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl5_8 <=> k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1))) | (~spl5_8 | ~spl5_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f121,f142])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    k4_relat_1(sK1) = k5_relat_1(k4_relat_1(sK1),k6_relat_1(k1_relat_1(sK1))) | ~v1_relat_1(k4_relat_1(sK1)) | ~spl5_8),
% 0.21/0.51    inference(superposition,[],[f43,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1)) | ~spl5_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f117])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    spl5_19 | ~spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f203,f64,f211])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~spl5_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f201,f66])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl5_1),
% 0.21/0.51    inference(superposition,[],[f137,f43])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    spl5_17 | ~spl5_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f169,f164,f197])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl5_12 <=> sP3(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    sK0 = k1_funct_1(sK1,sK4(sK1,sK0)) | ~spl5_12),
% 0.21/0.51    inference(resolution,[],[f166,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~sP3(X2,X0) | k1_funct_1(X0,sK4(X0,X2)) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    sP3(sK0,sK1) | ~spl5_12),
% 0.21/0.51    inference(avatar_component_clause,[],[f164])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ~spl5_16 | spl5_5 | ~spl5_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f129,f123,f101,f190])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl5_5 <=> sK0 = k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    sK0 != k1_funct_1(k5_relat_1(k4_relat_1(sK1),sK1),sK0) | (spl5_5 | ~spl5_9)),
% 0.21/0.51    inference(superposition,[],[f103,f125])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0) | spl5_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f101])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    spl5_15 | ~spl5_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f168,f164,f185])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    r2_hidden(sK4(sK1,sK0),k1_relat_1(sK1)) | ~spl5_12),
% 0.21/0.51    inference(resolution,[],[f166,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~sP3(X2,X0) | r2_hidden(sK4(X0,X2),k1_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    spl5_12 | ~spl5_1 | ~spl5_2 | ~spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f134,f96,f69,f64,f164])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    sP3(sK0,sK1) | (~spl5_1 | ~spl5_2 | ~spl5_4)),
% 0.21/0.51    inference(resolution,[],[f84,f98])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | sP3(X2,sK1)) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f81,f66])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X2] : (~v1_relat_1(sK1) | sP3(X2,sK1) | ~r2_hidden(X2,k2_relat_1(sK1))) ) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f71,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.51    inference(equality_resolution,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP3(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl5_11 | ~spl5_1 | ~spl5_2 | ~spl5_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f132,f123,f69,f64,f149])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    v1_funct_1(k4_relat_1(sK1)) | (~spl5_1 | ~spl5_2 | ~spl5_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f131,f66])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    v1_funct_1(k4_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl5_2 | ~spl5_9)),
% 0.21/0.51    inference(subsumption_resolution,[],[f130,f71])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    v1_funct_1(k4_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl5_9),
% 0.21/0.51    inference(superposition,[],[f48,f125])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl5_10 | ~spl5_7 | ~spl5_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f127,f123,f110,f140])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    v1_relat_1(k4_relat_1(sK1)) | (~spl5_7 | ~spl5_9)),
% 0.21/0.51    inference(superposition,[],[f112,f125])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl5_9 | ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f94,f74,f69,f64,f123])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f66])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1) | (~spl5_2 | ~spl5_3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f71])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1) | ~spl5_3),
% 0.21/0.51    inference(resolution,[],[f76,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl5_8 | ~spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f79,f64,f117])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    k1_relat_1(sK1) = k2_relat_1(k4_relat_1(sK1)) | ~spl5_1),
% 0.21/0.51    inference(resolution,[],[f66,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl5_7 | ~spl5_1 | ~spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f85,f69,f64,f110])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    v1_relat_1(k2_funct_1(sK1)) | (~spl5_1 | ~spl5_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f82,f66])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | v1_relat_1(k2_funct_1(sK1)) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f71,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    ~spl5_5 | ~spl5_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f105,f101])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl5_6 <=> sK0 = k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    sK0 != k1_funct_1(sK1,k1_funct_1(k2_funct_1(sK1),sK0)) | sK0 != k1_funct_1(k5_relat_1(k2_funct_1(sK1),sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) != X0 | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) != X0) & (r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f13])).
% 0.21/0.51  fof(f13,conjecture,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_funct_1)).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl5_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f36,f96])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    spl5_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f35,f74])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    spl5_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f34,f69])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl5_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f33,f64])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (20280)------------------------------
% 0.21/0.51  % (20280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20280)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (20280)Memory used [KB]: 11513
% 0.21/0.51  % (20280)Time elapsed: 0.069 s
% 0.21/0.51  % (20280)------------------------------
% 0.21/0.51  % (20280)------------------------------
% 0.21/0.51  % (20283)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (20276)Success in time 0.151 s
%------------------------------------------------------------------------------
