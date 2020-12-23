%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 117 expanded)
%              Number of leaves         :   22 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  193 ( 289 expanded)
%              Number of equality atoms :   45 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f399,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f56,f61,f71,f227,f235,f306,f322,f345,f369,f375,f397,f398])).

fof(f398,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(sK1,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f397,plain,
    ( spl4_19
    | spl4_18
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f396,f224,f315,f319])).

fof(f319,plain,
    ( spl4_19
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f315,plain,
    ( spl4_18
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f224,plain,
    ( spl4_10
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f396,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_10 ),
    inference(trivial_inequality_removal,[],[f395])).

fof(f395,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl4_10 ),
    inference(superposition,[],[f27,f226])).

fof(f226,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f224])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f375,plain,
    ( ~ spl4_5
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | ~ spl4_5
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f60,f34,f344,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f344,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl4_20
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f60,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_5
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f369,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k2_zfmisc_1(sK1,sK0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(sK1,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f345,plain,
    ( ~ spl4_20
    | spl4_1
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f323,f319,f39,f342])).

fof(f39,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f323,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_1
    | ~ spl4_19 ),
    inference(backward_demodulation,[],[f41,f321])).

fof(f321,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f319])).

fof(f41,plain,
    ( ~ v1_xboole_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f322,plain,
    ( spl4_18
    | spl4_19
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f313,f232,f319,f315])).

fof(f232,plain,
    ( spl4_11
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f313,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl4_11 ),
    inference(trivial_inequality_removal,[],[f312])).

fof(f312,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl4_11 ),
    inference(superposition,[],[f27,f234])).

fof(f234,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f232])).

fof(f306,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl4_17 ),
    inference(unit_resulting_resolution,[],[f34,f298])).

fof(f298,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl4_17
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f235,plain,
    ( spl4_11
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f228,f49,f44,f232])).

fof(f44,plain,
    ( spl4_2
  <=> r1_tarski(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f49,plain,
    ( spl4_3
  <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f228,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK0)
    | spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f51,f135])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1))
        | k1_xboole_0 = k2_zfmisc_1(sK1,X0) )
    | spl4_2 ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,
    ( ~ r1_tarski(sK1,sK3)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f51,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f227,plain,
    ( spl4_10
    | spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f217,f53,f44,f224])).

fof(f53,plain,
    ( spl4_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f217,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f184,f55])).

fof(f55,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3))
        | k1_xboole_0 = k2_zfmisc_1(X0,sK1) )
    | spl4_2 ),
    inference(resolution,[],[f32,f46])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f71,plain,
    ( ~ spl4_6
    | spl4_2 ),
    inference(avatar_split_clause,[],[f66,f44,f68])).

fof(f68,plain,
    ( spl4_6
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f66,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl4_2 ),
    inference(superposition,[],[f64,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f64,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k3_xboole_0(sK3,X0))
    | spl4_2 ),
    inference(resolution,[],[f30,f46])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f61,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f33,f58])).

fof(f33,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f56,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f17,f53,f49])).

fof(f17,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r1_tarski(X1,X3)
          & ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1,X2,X3] :
            ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
              | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
           => r1_tarski(X1,X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1,X2,X3] :
          ( ( r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2))
            | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
         => r1_tarski(X1,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

fof(f47,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f18,f44])).

fof(f18,plain,(
    ~ r1_tarski(sK1,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:01:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.48  % (30567)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.49  % (30558)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.49  % (30551)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (30556)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (30556)Refutation not found, incomplete strategy% (30556)------------------------------
% 0.20/0.49  % (30556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (30556)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (30556)Memory used [KB]: 6140
% 0.20/0.49  % (30556)Time elapsed: 0.085 s
% 0.20/0.49  % (30556)------------------------------
% 0.20/0.49  % (30556)------------------------------
% 0.20/0.49  % (30555)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (30575)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (30567)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f399,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f42,f47,f56,f61,f71,f227,f235,f306,f322,f345,f369,f375,f397,f398])).
% 0.20/0.50  fof(f398,plain,(
% 0.20/0.50    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(sK1,k1_xboole_0)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f397,plain,(
% 0.20/0.50    spl4_19 | spl4_18 | ~spl4_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f396,f224,f315,f319])).
% 0.20/0.50  fof(f319,plain,(
% 0.20/0.50    spl4_19 <=> k1_xboole_0 = sK0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    spl4_18 <=> k1_xboole_0 = sK1),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.50  fof(f224,plain,(
% 0.20/0.50    spl4_10 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.50  fof(f396,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl4_10),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f395])).
% 0.20/0.50  fof(f395,plain,(
% 0.20/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl4_10),
% 0.20/0.50    inference(superposition,[],[f27,f226])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl4_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f224])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.50  fof(f375,plain,(
% 0.20/0.50    ~spl4_5 | spl4_20),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f373])).
% 0.20/0.50  fof(f373,plain,(
% 0.20/0.50    $false | (~spl4_5 | spl4_20)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f60,f34,f344,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.50    inference(flattening,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.50  fof(f344,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | spl4_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f342])).
% 0.20/0.50  fof(f342,plain,(
% 0.20/0.50    spl4_20 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl4_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    spl4_5 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f369,plain,(
% 0.20/0.50    k1_xboole_0 != sK1 | k1_xboole_0 != k2_zfmisc_1(sK1,sK0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | r1_tarski(sK1,k1_xboole_0)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f345,plain,(
% 0.20/0.50    ~spl4_20 | spl4_1 | ~spl4_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f323,f319,f39,f342])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    spl4_1 <=> v1_xboole_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f323,plain,(
% 0.20/0.50    ~v1_xboole_0(k1_xboole_0) | (spl4_1 | ~spl4_19)),
% 0.20/0.50    inference(backward_demodulation,[],[f41,f321])).
% 0.20/0.50  fof(f321,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | ~spl4_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f319])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0) | spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f39])).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    spl4_18 | spl4_19 | ~spl4_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f313,f232,f319,f315])).
% 0.20/0.50  fof(f232,plain,(
% 0.20/0.50    spl4_11 <=> k1_xboole_0 = k2_zfmisc_1(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl4_11),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f312])).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl4_11),
% 0.20/0.50    inference(superposition,[],[f27,f234])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | ~spl4_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f232])).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    spl4_17),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f300])).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    $false | spl4_17),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f34,f298])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f296])).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    spl4_17 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    spl4_11 | spl4_2 | ~spl4_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f228,f49,f44,f232])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    spl4_2 <=> r1_tarski(sK1,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    spl4_3 <=> r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.50  fof(f228,plain,(
% 0.20/0.50    k1_xboole_0 = k2_zfmisc_1(sK1,sK0) | (spl4_2 | ~spl4_3)),
% 0.20/0.50    inference(resolution,[],[f51,f135])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(sK1,X0),k2_zfmisc_1(sK3,X1)) | k1_xboole_0 = k2_zfmisc_1(sK1,X0)) ) | spl4_2),
% 0.20/0.50    inference(resolution,[],[f31,f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK3) | spl4_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f44])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(X0,X2) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2)) | ~spl4_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f49])).
% 0.20/0.50  fof(f227,plain,(
% 0.20/0.50    spl4_10 | spl4_2 | ~spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f217,f53,f44,f224])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    spl4_4 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (spl4_2 | ~spl4_4)),
% 0.20/0.50    inference(resolution,[],[f184,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f53])).
% 0.20/0.50  fof(f184,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X1,sK3)) | k1_xboole_0 = k2_zfmisc_1(X0,sK1)) ) | spl4_2),
% 0.20/0.50    inference(resolution,[],[f32,f46])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | k1_xboole_0 = k2_zfmisc_1(X0,X1) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ~spl4_6 | spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f66,f44,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl4_6 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~r1_tarski(sK1,k1_xboole_0) | spl4_2),
% 0.20/0.50    inference(superposition,[],[f64,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(sK1,k3_xboole_0(sK3,X0))) ) | spl4_2),
% 0.20/0.50    inference(resolution,[],[f30,f46])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    spl4_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f33,f58])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    inference(equality_resolution,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    spl4_3 | spl4_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f17,f53,f49])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(sK3,sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0] : (? [X1,X2,X3] : (~r1_tarski(X1,X3) & (r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))) & ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.20/0.50    inference(negated_conjecture,[],[f8])).
% 0.20/0.50  fof(f8,conjecture,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1,X2,X3] : ((r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X3,X2)) | r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => r1_tarski(X1,X3)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ~spl4_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f18,f44])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ~r1_tarski(sK1,sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ~spl4_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f19,f39])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ~v1_xboole_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (30567)------------------------------
% 0.20/0.50  % (30567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (30567)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (30567)Memory used [KB]: 6396
% 0.20/0.50  % (30567)Time elapsed: 0.024 s
% 0.20/0.50  % (30567)------------------------------
% 0.20/0.50  % (30567)------------------------------
% 0.20/0.50  % (30547)Success in time 0.149 s
%------------------------------------------------------------------------------
