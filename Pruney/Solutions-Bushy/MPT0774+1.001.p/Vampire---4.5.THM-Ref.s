%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0774+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 302 expanded)
%              Number of leaves         :   20 ( 108 expanded)
%              Depth                    :   16
%              Number of atoms          :  452 ( 953 expanded)
%              Number of equality atoms :   25 (  56 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f692,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f60,f91,f96,f104,f109,f189,f201,f214,f222,f549,f581,f691])).

fof(f691,plain,
    ( ~ spl6_1
    | ~ spl6_4
    | spl6_5
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f690])).

fof(f690,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5
    | ~ spl6_7
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f689,f108])).

fof(f108,plain,
    ( r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_7
  <=> r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f689,plain,
    ( ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl6_1
    | ~ spl6_4
    | spl6_5
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f686,f90])).

fof(f90,plain,
    ( r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_4
  <=> r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f686,plain,
    ( ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0)
    | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl6_1
    | spl6_5
    | ~ spl6_12 ),
    inference(resolution,[],[f681,f95])).

fof(f95,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_5
  <=> r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f681,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,X0))
        | ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),X0)
        | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X0) )
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(resolution,[],[f678,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f678,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_zfmisc_1(X0,X0))
        | r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,X0)) )
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(superposition,[],[f586,f54])).

% (10404)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f54,plain,
    ( ! [X5] : k2_wellord1(sK1,X5) = k3_xboole_0(sK1,k2_zfmisc_1(X5,X5))
    | ~ spl6_1 ),
    inference(resolution,[],[f44,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(f44,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f586,plain,
    ( ! [X2] :
        ( r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k3_xboole_0(sK1,X2))
        | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X2) )
    | ~ spl6_12 ),
    inference(resolution,[],[f544,f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f544,plain,
    ( ! [X0] :
        ( sP5(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0,sK1)
        | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f543])).

fof(f543,plain,
    ( spl6_12
  <=> ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0)
        | sP5(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f581,plain,
    ( ~ spl6_1
    | spl6_3
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | ~ spl6_1
    | spl6_3
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f579,f59])).

fof(f59,plain,
    ( ~ v6_relat_2(k2_wellord1(sK1,sK0))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl6_3
  <=> v6_relat_2(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f579,plain,
    ( v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl6_1
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f578,f53])).

fof(f53,plain,
    ( ! [X4] : v1_relat_1(k2_wellord1(sK1,X4))
    | ~ spl6_1 ),
    inference(resolution,[],[f44,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k2_wellord1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f578,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl6_13 ),
    inference(trivial_inequality_removal,[],[f577])).

fof(f577,plain,
    ( sK2(k2_wellord1(sK1,sK0)) != sK2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl6_13 ),
    inference(superposition,[],[f22,f548])).

fof(f548,plain,
    ( sK2(k2_wellord1(sK1,sK0)) = sK3(k2_wellord1(sK1,sK0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl6_13
  <=> sK2(k2_wellord1(sK1,sK0)) = sK3(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f22,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

fof(f549,plain,
    ( spl6_12
    | spl6_13
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f535,f208,f183,f106,f101,f88,f47,f42,f546,f543])).

fof(f47,plain,
    ( spl6_2
  <=> v6_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f101,plain,
    ( spl6_6
  <=> r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f183,plain,
    ( spl6_8
  <=> r2_hidden(sK3(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f208,plain,
    ( spl6_10
  <=> r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f535,plain,
    ( ! [X0] :
        ( sK2(k2_wellord1(sK1,sK0)) = sK3(k2_wellord1(sK1,sK0))
        | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0)
        | sP5(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0,sK1) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f534,f90])).

fof(f534,plain,
    ( ! [X0] :
        ( sK2(k2_wellord1(sK1,sK0)) = sK3(k2_wellord1(sK1,sK0))
        | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0)
        | sP5(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0,sK1)
        | ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f533,f108])).

fof(f533,plain,
    ( ! [X0] :
        ( sK2(k2_wellord1(sK1,sK0)) = sK3(k2_wellord1(sK1,sK0))
        | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0)
        | sP5(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0,sK1)
        | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
        | ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_6
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f530,f210])).

fof(f210,plain,
    ( r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f208])).

fof(f530,plain,
    ( ! [X0] :
        ( sK2(k2_wellord1(sK1,sK0)) = sK3(k2_wellord1(sK1,sK0))
        | ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0)
        | sP5(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),X0,sK1)
        | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
        | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
        | ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0) )
    | ~ spl6_1
    | ~ spl6_2
    | spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f476,f103])).

fof(f103,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f476,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),X0),k2_wellord1(sK1,X1))
        | sK3(k2_wellord1(sK1,sK0)) = X0
        | ~ r2_hidden(k4_tarski(X0,sK3(k2_wellord1(sK1,sK0))),X2)
        | sP5(k4_tarski(X0,sK3(k2_wellord1(sK1,sK0))),X2,sK1)
        | ~ r2_hidden(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),X1) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(resolution,[],[f431,f38])).

fof(f431,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),X1),k2_zfmisc_1(X0,X0))
        | r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),X1),k2_wellord1(sK1,X0))
        | sK3(k2_wellord1(sK1,sK0)) = X1
        | ~ r2_hidden(k4_tarski(X1,sK3(k2_wellord1(sK1,sK0))),X2)
        | sP5(k4_tarski(X1,sK3(k2_wellord1(sK1,sK0))),X2,sK1)
        | ~ r2_hidden(X1,k3_relat_1(sK1)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(superposition,[],[f360,f54])).

fof(f360,plain,
    ( ! [X6,X8,X7] :
        ( r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),X6),k3_xboole_0(sK1,X7))
        | ~ r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),X6),X7)
        | sK3(k2_wellord1(sK1,sK0)) = X6
        | ~ r2_hidden(k4_tarski(X6,sK3(k2_wellord1(sK1,sK0))),X8)
        | sP5(k4_tarski(X6,sK3(k2_wellord1(sK1,sK0))),X8,sK1)
        | ~ r2_hidden(X6,k3_relat_1(sK1)) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(resolution,[],[f205,f40])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( sP5(k4_tarski(sK3(k2_wellord1(sK1,sK0)),X0),X1,sK1)
        | ~ r2_hidden(X0,k3_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),X0),X1)
        | sK3(k2_wellord1(sK1,sK0)) = X0
        | ~ r2_hidden(k4_tarski(X0,sK3(k2_wellord1(sK1,sK0))),X2)
        | sP5(k4_tarski(X0,sK3(k2_wellord1(sK1,sK0))),X2,sK1) )
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(resolution,[],[f185,f145])).

fof(f145,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK1))
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2)
        | sP5(k4_tarski(X0,X1),X2,sK1)
        | ~ r2_hidden(k4_tarski(X1,X0),X3)
        | sP5(k4_tarski(X1,X0),X3,sK1) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f117,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),sK1)
        | X0 = X1
        | ~ r2_hidden(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X1,k3_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),X2)
        | sP5(k4_tarski(X0,X1),X2,sK1) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f111,f29])).

fof(f111,plain,
    ( ! [X6,X7] :
        ( r2_hidden(k4_tarski(X7,X6),sK1)
        | ~ r2_hidden(X7,k3_relat_1(sK1))
        | X6 = X7
        | r2_hidden(k4_tarski(X6,X7),sK1)
        | ~ r2_hidden(X6,k3_relat_1(sK1)) )
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f55,f49])).

fof(f49,plain,
    ( v6_relat_2(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f55,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(X6,k3_relat_1(sK1))
        | ~ r2_hidden(X7,k3_relat_1(sK1))
        | X6 = X7
        | r2_hidden(k4_tarski(X6,X7),sK1)
        | r2_hidden(k4_tarski(X7,X6),sK1)
        | ~ v6_relat_2(sK1) )
    | ~ spl6_1 ),
    inference(resolution,[],[f44,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r2_hidden(X2,k3_relat_1(X0))
      | X1 = X2
      | r2_hidden(k4_tarski(X1,X2),X0)
      | r2_hidden(k4_tarski(X2,X1),X0)
      | ~ v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f185,plain,
    ( r2_hidden(sK3(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f183])).

fof(f222,plain,
    ( ~ spl6_1
    | spl6_3
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl6_1
    | spl6_3
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f220,f59])).

fof(f220,plain,
    ( v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl6_1
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f216,f53])).

fof(f216,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl6_11 ),
    inference(resolution,[],[f213,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f213,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl6_11
  <=> ! [X0] : ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f214,plain,
    ( spl6_10
    | spl6_11
    | ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f202,f57,f42,f212,f208])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X0)
        | r2_hidden(sK2(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
    | ~ spl6_1
    | spl6_3 ),
    inference(resolution,[],[f178,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f178,plain,
    ( ! [X0] :
        ( sP5(sK2(k2_wellord1(sK1,sK0)),X0,k3_relat_1(sK1))
        | ~ r2_hidden(sK2(k2_wellord1(sK1,sK0)),X0) )
    | ~ spl6_1
    | spl6_3 ),
    inference(resolution,[],[f141,f59])).

fof(f141,plain,
    ( ! [X2,X3] :
        ( v6_relat_2(k2_wellord1(sK1,X2))
        | sP5(sK2(k2_wellord1(sK1,X2)),X3,k3_relat_1(sK1))
        | ~ r2_hidden(sK2(k2_wellord1(sK1,X2)),X3) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f139,f53])).

fof(f139,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK2(k2_wellord1(sK1,X2)),X3)
        | sP5(sK2(k2_wellord1(sK1,X2)),X3,k3_relat_1(sK1))
        | ~ v1_relat_1(k2_wellord1(sK1,X2))
        | v6_relat_2(k2_wellord1(sK1,X2)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f84,f20])).

fof(f84,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,k3_relat_1(k2_wellord1(sK1,X4)))
        | ~ r2_hidden(X3,X5)
        | sP5(X3,X5,k3_relat_1(sK1)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f51,f29])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k3_relat_1(sK1))
        | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(sK1,X1))) )
    | ~ spl6_1 ),
    inference(resolution,[],[f44,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(f201,plain,
    ( ~ spl6_1
    | spl6_3
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl6_1
    | spl6_3
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f199,f59])).

fof(f199,plain,
    ( v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl6_1
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f195,f53])).

fof(f195,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl6_9 ),
    inference(resolution,[],[f188,f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v6_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f188,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),X0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl6_9
  <=> ! [X0] : ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f189,plain,
    ( spl6_8
    | spl6_9
    | ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f175,f57,f42,f187,f183])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),X0)
        | r2_hidden(sK3(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
    | ~ spl6_1
    | spl6_3 ),
    inference(resolution,[],[f174,f30])).

fof(f174,plain,
    ( ! [X0] :
        ( sP5(sK3(k2_wellord1(sK1,sK0)),X0,k3_relat_1(sK1))
        | ~ r2_hidden(sK3(k2_wellord1(sK1,sK0)),X0) )
    | ~ spl6_1
    | spl6_3 ),
    inference(resolution,[],[f140,f59])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( v6_relat_2(k2_wellord1(sK1,X0))
        | sP5(sK3(k2_wellord1(sK1,X0)),X1,k3_relat_1(sK1))
        | ~ r2_hidden(sK3(k2_wellord1(sK1,X0)),X1) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f138,f53])).

fof(f138,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK3(k2_wellord1(sK1,X0)),X1)
        | sP5(sK3(k2_wellord1(sK1,X0)),X1,k3_relat_1(sK1))
        | ~ v1_relat_1(k2_wellord1(sK1,X0))
        | v6_relat_2(k2_wellord1(sK1,X0)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f84,f21])).

fof(f109,plain,
    ( spl6_7
    | ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f99,f57,f42,f106])).

fof(f99,plain,
    ( r2_hidden(sK2(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl6_1
    | spl6_3 ),
    inference(resolution,[],[f76,f59])).

fof(f76,plain,
    ( ! [X1] :
        ( v6_relat_2(k2_wellord1(sK1,X1))
        | r2_hidden(sK2(k2_wellord1(sK1,X1)),X1) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f74,f53])).

fof(f74,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(k2_wellord1(sK1,X1)),X1)
        | ~ v1_relat_1(k2_wellord1(sK1,X1))
        | v6_relat_2(k2_wellord1(sK1,X1)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f20])).

fof(f52,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k3_relat_1(k2_wellord1(sK1,X3)))
        | r2_hidden(X2,X3) )
    | ~ spl6_1 ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,
    ( ~ spl6_6
    | ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f98,f57,f42,f101])).

fof(f98,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f62,f53])).

fof(f62,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k2_wellord1(sK1,sK0)),sK2(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | spl6_3 ),
    inference(resolution,[],[f59,f24])).

fof(f24,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r2_hidden(k4_tarski(sK3(X0),sK2(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f96,plain,
    ( ~ spl6_5
    | ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f86,f57,f42,f93])).

fof(f86,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f61,f53])).

fof(f61,plain,
    ( ~ r2_hidden(k4_tarski(sK2(k2_wellord1(sK1,sK0)),sK3(k2_wellord1(sK1,sK0))),k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | spl6_3 ),
    inference(resolution,[],[f59,f23])).

fof(f23,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,
    ( spl6_4
    | ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f85,f57,f42,f88])).

fof(f85,plain,
    ( r2_hidden(sK3(k2_wellord1(sK1,sK0)),sK0)
    | ~ spl6_1
    | spl6_3 ),
    inference(resolution,[],[f75,f59])).

fof(f75,plain,
    ( ! [X0] :
        ( v6_relat_2(k2_wellord1(sK1,X0))
        | r2_hidden(sK3(k2_wellord1(sK1,X0)),X0) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f73,f53])).

fof(f73,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k2_wellord1(sK1,X0)),X0)
        | ~ v1_relat_1(k2_wellord1(sK1,X0))
        | v6_relat_2(k2_wellord1(sK1,X0)) )
    | ~ spl6_1 ),
    inference(resolution,[],[f52,f21])).

fof(f60,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f18,f57])).

fof(f18,plain,(
    ~ v6_relat_2(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ v6_relat_2(k2_wellord1(X1,X0))
      & v6_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ v6_relat_2(k2_wellord1(X1,X0))
      & v6_relat_2(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v6_relat_2(X1)
         => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
       => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_wellord1)).

fof(f50,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f17,f47])).

fof(f17,plain,(
    v6_relat_2(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f45,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
