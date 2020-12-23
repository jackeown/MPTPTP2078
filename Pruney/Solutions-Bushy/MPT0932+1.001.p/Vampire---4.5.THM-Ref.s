%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0932+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  140 ( 200 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f41,f45,f50,f54,f59])).

fof(f59,plain,
    ( ~ spl3_1
    | spl3_3
    | spl3_5
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f57,f49])).

fof(f49,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),a_2_0_mcart_1(sK0,k1_mcart_1(sK1)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_5
  <=> r2_hidden(k2_mcart_1(sK1),a_2_0_mcart_1(sK0,k1_mcart_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f57,plain,
    ( r2_hidden(k2_mcart_1(sK1),a_2_0_mcart_1(sK0,k1_mcart_1(sK1)))
    | ~ spl3_1
    | spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f56,f40])).

fof(f40,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f56,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(k2_mcart_1(sK1),a_2_0_mcart_1(sK0,k1_mcart_1(sK1)))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f28,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f55,plain,
    ( ~ v1_relat_1(sK0)
    | v1_xboole_0(sK0)
    | r2_hidden(k2_mcart_1(sK1),a_2_0_mcart_1(sK0,k1_mcart_1(sK1)))
    | ~ spl3_6 ),
    inference(resolution,[],[f53,f25])).

fof(f25,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,X1)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1)
      | r2_hidden(k2_mcart_1(X3),a_2_0_mcart_1(X1,k1_mcart_1(X3))) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X3,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | k1_mcart_1(X3) != X2
      | r2_hidden(k2_mcart_1(X3),a_2_0_mcart_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_relat_1(X1)
      | ~ m1_subset_1(X3,X1)
      | k2_mcart_1(X3) != X0
      | k1_mcart_1(X3) != X2
      | r2_hidden(X0,a_2_0_mcart_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) )
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_relat_1(X1)
        & ~ v1_xboole_0(X1) )
     => ( r2_hidden(X0,a_2_0_mcart_1(X1,X2))
      <=> ? [X3] :
            ( k1_mcart_1(X3) = X2
            & k2_mcart_1(X3) = X0
            & m1_subset_1(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_mcart_1)).

fof(f53,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f54,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f35,f32,f52])).

% (10374)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f32,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f35,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f33,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f50,plain,
    ( ~ spl3_5
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f46,f43,f32,f27,f48])).

fof(f43,plain,
    ( spl3_4
  <=> r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f46,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),a_2_0_mcart_1(sK0,k1_mcart_1(sK1)))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4 ),
    inference(forward_demodulation,[],[f44,f37])).

fof(f37,plain,
    ( ! [X0] : k11_relat_1(sK0,X0) = a_2_0_mcart_1(sK0,X0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f30,f36])).

fof(f36,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f30,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | k11_relat_1(sK0,X0) = a_2_0_mcart_1(sK0,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f28,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_xboole_0(X0)
      | k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] : k11_relat_1(X0,X1) = a_2_0_mcart_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_mcart_1)).

fof(f44,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f45,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f15,f43])).

fof(f15,plain,(
    ~ r2_hidden(k2_mcart_1(sK1),k11_relat_1(sK0,k1_mcart_1(sK1))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1)))
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r2_hidden(k2_mcart_1(X1),k11_relat_1(X0,k1_mcart_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_mcart_1)).

fof(f41,plain,
    ( ~ spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f36,f32,f39])).

fof(f34,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f32])).

fof(f14,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f27])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
