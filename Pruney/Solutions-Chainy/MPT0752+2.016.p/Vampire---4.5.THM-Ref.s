%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 195 expanded)
%              Number of leaves         :   26 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  338 ( 583 expanded)
%              Number of equality atoms :  105 ( 197 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f106,f113,f129,f194,f208,f285])).

fof(f285,plain,
    ( spl3_4
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl3_4
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f281,f93])).

fof(f93,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_4
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f281,plain,
    ( v5_ordinal1(k1_xboole_0)
    | ~ spl3_10 ),
    inference(superposition,[],[f67,f242])).

fof(f242,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f240,f64])).

fof(f64,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v5_ordinal1(sK1(X0))
      & v1_funct_1(sK1(X0))
      & v5_relat_1(sK1(X0),X0)
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v5_ordinal1(X1)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( v5_ordinal1(sK1(X0))
        & v1_funct_1(sK1(X0))
        & v5_relat_1(sK1(X0),X0)
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] :
      ( v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).

fof(f240,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ v1_relat_1(sK1(k1_xboole_0))
    | ~ spl3_10 ),
    inference(resolution,[],[f192,f65])).

fof(f65,plain,(
    ! [X0] : v5_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f41])).

fof(f192,plain,
    ( ! [X5] :
        ( ~ v5_relat_1(X5,k1_xboole_0)
        | k1_xboole_0 = X5
        | ~ v1_relat_1(X5) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_10
  <=> ! [X5] :
        ( k1_xboole_0 = X5
        | ~ v5_relat_1(X5,k1_xboole_0)
        | ~ v1_relat_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f67,plain,(
    ! [X0] : v5_ordinal1(sK1(X0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f208,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f206,f193])).

fof(f193,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_7
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f206,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f205,f122])).

fof(f122,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f120,f50])).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f120,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k6_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f115,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f115,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f114,f50])).

fof(f114,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f58,f98])).

fof(f98,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(subsumption_resolution,[],[f97,f50])).

fof(f97,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f81,f52])).

% (16503)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f52,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f81,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f58,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f205,plain,(
    k1_xboole_0 = k2_relat_1(k6_relat_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f200,f50])).

fof(f200,plain,
    ( k1_xboole_0 = k2_relat_1(k6_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k6_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f56,f117])).

fof(f117,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f116,f50])).

fof(f116,plain,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f59,f98])).

fof(f59,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f194,plain,
    ( spl3_10
    | ~ spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f189,f83,f149,f191])).

fof(f83,plain,
    ( spl3_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f189,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
        | k1_xboole_0 = X5
        | ~ v1_relat_1(X5)
        | ~ v5_relat_1(X5,k1_xboole_0) )
    | ~ spl3_1 ),
    inference(inner_rewriting,[],[f177])).

fof(f177,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
        | k1_xboole_0 = X5
        | ~ v1_relat_1(X5)
        | ~ v5_relat_1(X5,k2_relat_1(k1_xboole_0)) )
    | ~ spl3_1 ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
        | k1_xboole_0 = X5
        | ~ v1_relat_1(X5)
        | ~ v5_relat_1(X5,k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(X5) )
    | ~ spl3_1 ),
    inference(superposition,[],[f63,f157])).

fof(f157,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) = k2_relat_1(k1_xboole_0)
        | ~ v5_relat_1(X0,k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f152,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f152,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k2_relat_1(k1_xboole_0))
        | k2_relat_1(k1_xboole_0) = X1 )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f140,f110])).

fof(f110,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f140,plain,
    ( ! [X1] :
        ( k2_relat_1(k1_xboole_0) = X1
        | ~ r1_tarski(X1,k2_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_1 ),
    inference(superposition,[],[f71,f137])).

fof(f137,plain,
    ( ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f136,f50])).

fof(f136,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f134,f110])).

fof(f134,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f70,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f129,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f126,f90])).

fof(f90,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_3
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f126,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f52,f122])).

fof(f113,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f87,f68])).

fof(f68,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t206_relat_1)).

fof(f87,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_2
  <=> v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f106,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f101,f50])).

fof(f101,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f100,f84])).

fof(f84,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f100,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f69,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f94,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f49,f92,f89,f86,f83])).

fof(f49,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ~ v5_ordinal1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
   => ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,sK0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:05:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (16505)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.44  % (16507)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.44  % (16501)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.44  % (16499)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.44  % (16504)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.44  % (16501)Refutation not found, incomplete strategy% (16501)------------------------------
% 0.20/0.44  % (16501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (16501)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (16501)Memory used [KB]: 1663
% 0.20/0.44  % (16501)Time elapsed: 0.046 s
% 0.20/0.44  % (16501)------------------------------
% 0.20/0.44  % (16501)------------------------------
% 0.20/0.44  % (16509)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.44  % (16509)Refutation not found, incomplete strategy% (16509)------------------------------
% 0.20/0.44  % (16509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (16509)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (16509)Memory used [KB]: 6012
% 0.20/0.44  % (16509)Time elapsed: 0.002 s
% 0.20/0.44  % (16509)------------------------------
% 0.20/0.44  % (16509)------------------------------
% 0.20/0.44  % (16499)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f286,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f94,f106,f113,f129,f194,f208,f285])).
% 0.20/0.44  fof(f285,plain,(
% 0.20/0.44    spl3_4 | ~spl3_10),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f284])).
% 0.20/0.44  fof(f284,plain,(
% 0.20/0.44    $false | (spl3_4 | ~spl3_10)),
% 0.20/0.44    inference(subsumption_resolution,[],[f281,f93])).
% 0.20/0.44  fof(f93,plain,(
% 0.20/0.44    ~v5_ordinal1(k1_xboole_0) | spl3_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f92])).
% 0.20/0.44  fof(f92,plain,(
% 0.20/0.44    spl3_4 <=> v5_ordinal1(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.44  fof(f281,plain,(
% 0.20/0.44    v5_ordinal1(k1_xboole_0) | ~spl3_10),
% 0.20/0.44    inference(superposition,[],[f67,f242])).
% 0.20/0.44  fof(f242,plain,(
% 0.20/0.44    k1_xboole_0 = sK1(k1_xboole_0) | ~spl3_10),
% 0.20/0.44    inference(subsumption_resolution,[],[f240,f64])).
% 0.20/0.44  fof(f64,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f41])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ! [X0] : (v5_ordinal1(sK1(X0)) & v1_funct_1(sK1(X0)) & v5_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0)))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ! [X0] : (? [X1] : (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v5_ordinal1(sK1(X0)) & v1_funct_1(sK1(X0)) & v5_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0))))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f17,axiom,(
% 0.20/0.44    ! [X0] : ? [X1] : (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).
% 0.20/0.44  fof(f240,plain,(
% 0.20/0.44    k1_xboole_0 = sK1(k1_xboole_0) | ~v1_relat_1(sK1(k1_xboole_0)) | ~spl3_10),
% 0.20/0.44    inference(resolution,[],[f192,f65])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    ( ! [X0] : (v5_relat_1(sK1(X0),X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f41])).
% 0.20/0.44  fof(f192,plain,(
% 0.20/0.44    ( ! [X5] : (~v5_relat_1(X5,k1_xboole_0) | k1_xboole_0 = X5 | ~v1_relat_1(X5)) ) | ~spl3_10),
% 0.20/0.44    inference(avatar_component_clause,[],[f191])).
% 0.20/0.44  fof(f191,plain,(
% 0.20/0.44    spl3_10 <=> ! [X5] : (k1_xboole_0 = X5 | ~v5_relat_1(X5,k1_xboole_0) | ~v1_relat_1(X5))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    ( ! [X0] : (v5_ordinal1(sK1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f41])).
% 0.20/0.44  fof(f208,plain,(
% 0.20/0.44    spl3_7),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f207])).
% 0.20/0.44  fof(f207,plain,(
% 0.20/0.44    $false | spl3_7),
% 0.20/0.44    inference(subsumption_resolution,[],[f206,f193])).
% 0.20/0.44  fof(f193,plain,(
% 0.20/0.44    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl3_7),
% 0.20/0.44    inference(avatar_component_clause,[],[f149])).
% 0.20/0.44  fof(f149,plain,(
% 0.20/0.44    spl3_7 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.44  fof(f206,plain,(
% 0.20/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(forward_demodulation,[],[f205,f122])).
% 0.20/0.44  fof(f122,plain,(
% 0.20/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(subsumption_resolution,[],[f120,f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(k1_xboole_0))),
% 0.20/0.44    inference(superposition,[],[f115,f55])).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f114,f50])).
% 0.20/0.44  fof(f114,plain,(
% 0.20/0.44    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(superposition,[],[f58,f98])).
% 0.20/0.44  fof(f98,plain,(
% 0.20/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f97,f50])).
% 0.20/0.44  fof(f97,plain,(
% 0.20/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f81,f52])).
% 0.20/0.44  % (16503)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f15])).
% 0.20/0.44  fof(f15,axiom,(
% 0.20/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.44  fof(f81,plain,(
% 0.20/0.44    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(equality_resolution,[],[f74])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f48])).
% 0.20/0.44  fof(f48,plain,(
% 0.20/0.44    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f46,plain,(
% 0.20/0.44    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(rectify,[],[f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f44])).
% 0.20/0.44  fof(f44,plain,(
% 0.20/0.44    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(nnf_transformation,[],[f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f36])).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.44    inference(ennf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,axiom,(
% 0.20/0.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.44  fof(f205,plain,(
% 0.20/0.44    k1_xboole_0 = k2_relat_1(k6_relat_1(k1_xboole_0))),
% 0.20/0.44    inference(subsumption_resolution,[],[f200,f50])).
% 0.20/0.44  fof(f200,plain,(
% 0.20/0.44    k1_xboole_0 = k2_relat_1(k6_relat_1(k1_xboole_0)) | ~v1_relat_1(k6_relat_1(k1_xboole_0))),
% 0.20/0.44    inference(superposition,[],[f56,f117])).
% 0.20/0.44  fof(f117,plain,(
% 0.20/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.44    inference(subsumption_resolution,[],[f116,f50])).
% 0.20/0.44  fof(f116,plain,(
% 0.20/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(superposition,[],[f59,f98])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).
% 0.20/0.44  fof(f194,plain,(
% 0.20/0.44    spl3_10 | ~spl3_7 | ~spl3_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f189,f83,f149,f191])).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    spl3_1 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.44  fof(f189,plain,(
% 0.20/0.44    ( ! [X5] : (k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = X5 | ~v1_relat_1(X5) | ~v5_relat_1(X5,k1_xboole_0)) ) | ~spl3_1),
% 0.20/0.44    inference(inner_rewriting,[],[f177])).
% 0.20/0.44  fof(f177,plain,(
% 0.20/0.44    ( ! [X5] : (k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = X5 | ~v1_relat_1(X5) | ~v5_relat_1(X5,k2_relat_1(k1_xboole_0))) ) | ~spl3_1),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f170])).
% 0.20/0.44  fof(f170,plain,(
% 0.20/0.44    ( ! [X5] : (k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 = X5 | ~v1_relat_1(X5) | ~v5_relat_1(X5,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(X5)) ) | ~spl3_1),
% 0.20/0.44    inference(superposition,[],[f63,f157])).
% 0.20/0.44  fof(f157,plain,(
% 0.20/0.44    ( ! [X0] : (k2_relat_1(X0) = k2_relat_1(k1_xboole_0) | ~v5_relat_1(X0,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(X0)) ) | ~spl3_1),
% 0.20/0.44    inference(resolution,[],[f152,f72])).
% 0.20/0.44  fof(f72,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f43])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(nnf_transformation,[],[f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.44  fof(f152,plain,(
% 0.20/0.44    ( ! [X1] : (~r1_tarski(X1,k2_relat_1(k1_xboole_0)) | k2_relat_1(k1_xboole_0) = X1) ) | ~spl3_1),
% 0.20/0.44    inference(subsumption_resolution,[],[f140,f110])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    v1_relat_1(k1_xboole_0) | ~spl3_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f83])).
% 0.20/0.44  fof(f140,plain,(
% 0.20/0.44    ( ! [X1] : (k2_relat_1(k1_xboole_0) = X1 | ~r1_tarski(X1,k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl3_1),
% 0.20/0.44    inference(superposition,[],[f71,f137])).
% 0.20/0.44  fof(f137,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)) ) | ~spl3_1),
% 0.20/0.44    inference(subsumption_resolution,[],[f136,f50])).
% 0.20/0.44  fof(f136,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) | ~v1_relat_1(k6_relat_1(X0))) ) | ~spl3_1),
% 0.20/0.44    inference(subsumption_resolution,[],[f134,f110])).
% 0.20/0.44  fof(f134,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.44    inference(superposition,[],[f70,f60])).
% 0.20/0.44  fof(f60,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0] : ((k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f32])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.44  fof(f71,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f34])).
% 0.20/0.44  fof(f34,plain,(
% 0.20/0.44    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(flattening,[],[f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ! [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(flattening,[],[f29])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.44  fof(f129,plain,(
% 0.20/0.44    spl3_3),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f128])).
% 0.20/0.44  fof(f128,plain,(
% 0.20/0.44    $false | spl3_3),
% 0.20/0.44    inference(subsumption_resolution,[],[f126,f90])).
% 0.20/0.44  fof(f90,plain,(
% 0.20/0.44    ~v1_funct_1(k1_xboole_0) | spl3_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f89])).
% 0.20/0.44  fof(f89,plain,(
% 0.20/0.44    spl3_3 <=> v1_funct_1(k1_xboole_0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.44  fof(f126,plain,(
% 0.20/0.44    v1_funct_1(k1_xboole_0)),
% 0.20/0.44    inference(superposition,[],[f52,f122])).
% 0.20/0.44  fof(f113,plain,(
% 0.20/0.44    spl3_2),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.44  fof(f112,plain,(
% 0.20/0.44    $false | spl3_2),
% 0.20/0.44    inference(subsumption_resolution,[],[f87,f68])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ! [X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.20/0.44    inference(rectify,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.20/0.44    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.44  fof(f10,axiom,(
% 0.20/0.44    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t206_relat_1)).
% 0.20/0.44  fof(f87,plain,(
% 0.20/0.44    ~v5_relat_1(k1_xboole_0,sK0) | spl3_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f86])).
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    spl3_2 <=> v5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    spl3_1),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f102])).
% 0.20/0.44  fof(f102,plain,(
% 0.20/0.44    $false | spl3_1),
% 0.20/0.44    inference(resolution,[],[f101,f50])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_relat_1(X0)) ) | spl3_1),
% 0.20/0.44    inference(subsumption_resolution,[],[f100,f84])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    ~v1_relat_1(k1_xboole_0) | spl3_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f83])).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(duplicate_literal_removal,[],[f99])).
% 0.20/0.44  fof(f99,plain,(
% 0.20/0.44    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(superposition,[],[f69,f57])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    ( ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f31])).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.20/0.44  fof(f94,plain,(
% 0.20/0.44    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.20/0.44    inference(avatar_split_clause,[],[f49,f92,f89,f86,f83])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(cnf_transformation,[],[f39])).
% 0.20/0.44  fof(f39,plain,(
% 0.20/0.44    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f38])).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) => (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.20/0.44    inference(ennf_transformation,[],[f19])).
% 0.20/0.44  fof(f19,negated_conjecture,(
% 0.20/0.44    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.20/0.44    inference(negated_conjecture,[],[f18])).
% 0.20/0.44  fof(f18,conjecture,(
% 0.20/0.44    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (16499)------------------------------
% 0.20/0.44  % (16499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (16499)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (16499)Memory used [KB]: 10618
% 0.20/0.44  % (16499)Time elapsed: 0.048 s
% 0.20/0.44  % (16499)------------------------------
% 0.20/0.44  % (16499)------------------------------
% 0.20/0.45  % (16495)Success in time 0.095 s
%------------------------------------------------------------------------------
