%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 196 expanded)
%              Number of leaves         :   30 (  77 expanded)
%              Depth                    :   14
%              Number of atoms          :  368 ( 574 expanded)
%              Number of equality atoms :   94 ( 155 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f102,f104,f121,f125,f129,f139,f146,f188,f195,f242,f245])).

fof(f245,plain,
    ( ~ spl3_17
    | ~ spl3_18 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(resolution,[],[f241,f194])).

% (5986)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f194,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl3_17
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f241,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f240])).

fof(f240,plain,
    ( spl3_18
  <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f242,plain,
    ( ~ spl3_3
    | ~ spl3_2
    | ~ spl3_11
    | ~ spl3_10
    | spl3_18
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f235,f119,f72,f240,f123,f127,f76,f80])).

fof(f80,plain,
    ( spl3_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f76,plain,
    ( spl3_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f127,plain,
    ( spl3_11
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f123,plain,
    ( spl3_10
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f72,plain,
    ( spl3_1
  <=> v5_funct_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f119,plain,
    ( spl3_9
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f235,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f234,f120])).

fof(f120,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f234,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | spl3_1 ),
    inference(resolution,[],[f57,f73])).

fof(f73,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).

fof(f195,plain,
    ( ~ spl3_11
    | spl3_17
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f191,f185,f119,f193,f127])).

fof(f185,plain,
    ( spl3_16
  <=> ! [X1] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f190,f120])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_16 ),
    inference(trivial_inequality_removal,[],[f189])).

fof(f189,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_16 ),
    inference(superposition,[],[f61,f186])).

fof(f186,plain,
    ( ! [X1] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f185])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f188,plain,
    ( ~ spl3_11
    | spl3_16
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f183,f143,f127,f185,f127])).

fof(f143,plain,
    ( spl3_13
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f183,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(superposition,[],[f55,f174])).

fof(f174,plain,
    ( ! [X3] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f173,f144])).

fof(f144,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f173,plain,
    ( ! [X3] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X3)
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f172,f160])).

fof(f160,plain,
    ( ! [X3] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X3)
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f159,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k5_relat_1(k6_relat_1(X0),k1_xboole_0) ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f159,plain,
    ( ! [X3] : k7_relat_1(k1_xboole_0,X3) = k5_relat_1(k6_relat_1(X3),k1_xboole_0)
    | ~ spl3_11 ),
    inference(resolution,[],[f59,f128])).

fof(f128,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f172,plain,
    ( ! [X3] : k2_relat_1(k7_relat_1(k1_xboole_0,X3)) = k9_relat_1(k1_xboole_0,X3)
    | ~ spl3_11 ),
    inference(resolution,[],[f60,f128])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f146,plain,
    ( ~ spl3_11
    | spl3_13
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f141,f137,f143,f127])).

fof(f137,plain,
    ( spl3_12
  <=> k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f141,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_12 ),
    inference(superposition,[],[f50,f138])).

fof(f138,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f139,plain,
    ( ~ spl3_11
    | spl3_12
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f133,f119,f137,f127])).

fof(f133,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_9 ),
    inference(superposition,[],[f52,f120])).

fof(f52,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f129,plain,
    ( spl3_11
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f109,f99,f127])).

fof(f99,plain,
    ( spl3_6
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f109,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f46,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f125,plain,
    ( spl3_10
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f108,f99,f123])).

fof(f108,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f48,f100])).

fof(f48,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f121,plain,
    ( spl3_9
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f107,f99,f119])).

fof(f107,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(superposition,[],[f84,f100])).

fof(f84,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(global_subsumption,[],[f46,f48,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = X0
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | k6_relat_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f104,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f97,f46])).

fof(f97,plain,
    ( ~ v1_relat_1(k6_relat_1(k1_xboole_0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_5
  <=> v1_relat_1(k6_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f102,plain,
    ( ~ spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f94,f99,f96])).

fof(f94,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k6_relat_1(k1_xboole_0)) ),
    inference(superposition,[],[f49,f92])).

fof(f92,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(global_subsumption,[],[f46,f91])).

fof(f91,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f51,f84])).

fof(f51,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f82,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f43,f80])).

fof(f43,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).

fof(f78,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f44,f76])).

fof(f44,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f45,f72])).

fof(f45,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (6006)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (5998)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (5998)Refutation not found, incomplete strategy% (5998)------------------------------
% 0.21/0.46  % (5998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (5998)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (5998)Memory used [KB]: 6012
% 0.21/0.46  % (5998)Time elapsed: 0.002 s
% 0.21/0.46  % (5998)------------------------------
% 0.21/0.46  % (5998)------------------------------
% 0.21/0.46  % (6006)Refutation not found, incomplete strategy% (6006)------------------------------
% 0.21/0.46  % (6006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (6006)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (6006)Memory used [KB]: 10490
% 0.21/0.46  % (6006)Time elapsed: 0.055 s
% 0.21/0.46  % (6006)------------------------------
% 0.21/0.46  % (6006)------------------------------
% 0.21/0.47  % (5999)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (5993)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (5992)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (5988)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (5992)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f74,f78,f82,f102,f104,f121,f125,f129,f139,f146,f188,f195,f242,f245])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    ~spl3_17 | ~spl3_18),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f243])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    $false | (~spl3_17 | ~spl3_18)),
% 0.21/0.49    inference(resolution,[],[f241,f194])).
% 0.21/0.49  % (5986)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f193])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    spl3_17 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f240])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    spl3_18 <=> r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    ~spl3_3 | ~spl3_2 | ~spl3_11 | ~spl3_10 | spl3_18 | spl3_1 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f235,f119,f72,f240,f123,f127,f76,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl3_3 <=> v1_relat_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl3_2 <=> v1_funct_1(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl3_11 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl3_10 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl3_1 <=> v5_funct_1(k1_xboole_0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl3_9 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | (spl3_1 | ~spl3_9)),
% 0.21/0.49    inference(forward_demodulation,[],[f234,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f119])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | spl3_1),
% 0.21/0.49    inference(resolution,[],[f57,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ~v5_funct_1(k1_xboole_0,sK0) | spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(rectify,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_funct_1)).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    ~spl3_11 | spl3_17 | ~spl3_9 | ~spl3_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f191,f185,f119,f193,f127])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl3_16 <=> ! [X1] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl3_9 | ~spl3_16)),
% 0.21/0.49    inference(forward_demodulation,[],[f190,f120])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl3_16),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f189])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl3_16),
% 0.21/0.49    inference(superposition,[],[f61,f186])).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    ( ! [X1] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X1)) ) | ~spl3_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    ~spl3_11 | spl3_16 | ~spl3_11 | ~spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f183,f143,f127,f185,f127])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl3_13 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl3_11 | ~spl3_13)),
% 0.21/0.49    inference(superposition,[],[f55,f174])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X3] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)) ) | (~spl3_11 | ~spl3_13)),
% 0.21/0.49    inference(forward_demodulation,[],[f173,f144])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    ( ! [X3] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X3)) ) | ~spl3_11),
% 0.21/0.49    inference(forward_demodulation,[],[f172,f160])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ( ! [X3] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X3)) ) | ~spl3_11),
% 0.21/0.49    inference(forward_demodulation,[],[f159,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k6_relat_1(X0),k1_xboole_0)) )),
% 0.21/0.49    inference(resolution,[],[f54,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : ((k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ( ! [X3] : (k7_relat_1(k1_xboole_0,X3) = k5_relat_1(k6_relat_1(X3),k1_xboole_0)) ) | ~spl3_11),
% 0.21/0.49    inference(resolution,[],[f59,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    ( ! [X3] : (k2_relat_1(k7_relat_1(k1_xboole_0,X3)) = k9_relat_1(k1_xboole_0,X3)) ) | ~spl3_11),
% 0.21/0.49    inference(resolution,[],[f60,f128])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ~spl3_11 | spl3_13 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f141,f137,f143,f127])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl3_12 <=> k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl3_12),
% 0.21/0.49    inference(superposition,[],[f50,f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ~spl3_11 | spl3_12 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f133,f119,f137,f127])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl3_9),
% 0.21/0.49    inference(superposition,[],[f52,f120])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl3_11 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f109,f99,f127])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl3_6 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    v1_relat_1(k1_xboole_0) | ~spl3_6),
% 0.21/0.49    inference(superposition,[],[f46,f100])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f99])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl3_10 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f108,f99,f123])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    v1_funct_1(k1_xboole_0) | ~spl3_6),
% 0.21/0.49    inference(superposition,[],[f48,f100])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl3_9 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f107,f99,f119])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_6),
% 0.21/0.49    inference(superposition,[],[f84,f100])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(global_subsumption,[],[f46,f48,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | k6_relat_1(X0) != X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f40,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(rectify,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    $false | spl3_5),
% 0.21/0.49    inference(resolution,[],[f97,f46])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~v1_relat_1(k6_relat_1(k1_xboole_0)) | spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_5 <=> v1_relat_1(k6_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ~spl3_5 | spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f94,f99,f96])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~v1_relat_1(k6_relat_1(k1_xboole_0))),
% 0.21/0.49    inference(superposition,[],[f49,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.49    inference(global_subsumption,[],[f46,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(superposition,[],[f51,f84])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f80])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v1_relat_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f14])).
% 0.21/0.49  fof(f14,conjecture,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_1)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f76])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v1_funct_1(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ~spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f72])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ~v5_funct_1(k1_xboole_0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (5992)------------------------------
% 0.21/0.49  % (5992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5992)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (5992)Memory used [KB]: 10746
% 0.21/0.49  % (5992)Time elapsed: 0.071 s
% 0.21/0.49  % (5992)------------------------------
% 0.21/0.49  % (5992)------------------------------
% 0.21/0.49  % (5985)Success in time 0.135 s
%------------------------------------------------------------------------------
