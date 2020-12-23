%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 110 expanded)
%              Number of leaves         :   17 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  181 ( 315 expanded)
%              Number of equality atoms :   38 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f69,f89,f108,f137,f148,f161])).

fof(f161,plain,
    ( ~ spl3_6
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl3_6
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f68,f36,f36,f147,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

% (12818)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f147,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_16
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
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

fof(f68,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_6
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f148,plain,
    ( ~ spl3_16
    | spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f138,f134,f41,f145])).

fof(f41,plain,
    ( spl3_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f134,plain,
    ( spl3_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f138,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_1
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f43,f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f134])).

fof(f43,plain,
    ( ~ v1_xboole_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f137,plain,
    ( spl3_15
    | spl3_2
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f130,f105,f51,f46,f134])).

fof(f46,plain,
    ( spl3_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,
    ( spl3_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f105,plain,
    ( spl3_11
  <=> sK1 = k1_tarski(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f130,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f129,f53])).

fof(f53,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | ~ spl3_11 ),
    inference(superposition,[],[f31,f107])).

fof(f107,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f108,plain,
    ( ~ spl3_4
    | spl3_5
    | spl3_11
    | spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f103,f86,f61,f105,f61,f56])).

fof(f56,plain,
    ( spl3_4
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f61,plain,
    ( spl3_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f86,plain,
    ( spl3_8
  <=> sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f103,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1)
    | spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f102,f88])).

fof(f88,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f102,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1)
    | spl3_5 ),
    inference(resolution,[],[f91,f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f91,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK1)
        | k1_tarski(X1) = k6_domain_1(sK1,X1) )
    | spl3_5 ),
    inference(resolution,[],[f27,f63])).

fof(f63,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f89,plain,
    ( spl3_5
    | spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f84,f56,f86,f61])).

fof(f84,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f25,f58])).

fof(f58,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f64,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f17,f61])).

fof(f17,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f59,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f56])).

fof(f18,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f54,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f51])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n007.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 20:32:06 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.47  % (12804)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.47  % (12813)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.47  % (12804)Refutation not found, incomplete strategy% (12804)------------------------------
% 0.19/0.47  % (12804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (12804)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (12804)Memory used [KB]: 10618
% 0.19/0.47  % (12804)Time elapsed: 0.068 s
% 0.19/0.47  % (12804)------------------------------
% 0.19/0.47  % (12804)------------------------------
% 0.19/0.48  % (12806)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.48  % (12813)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f162,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f69,f89,f108,f137,f148,f161])).
% 0.19/0.48  fof(f161,plain,(
% 0.19/0.48    ~spl3_6 | spl3_16),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f158])).
% 0.19/0.48  fof(f158,plain,(
% 0.19/0.48    $false | (~spl3_6 | spl3_16)),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f68,f36,f36,f147,f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~r1_tarski(X2,X0) | ~r1_tarski(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f16])).
% 0.19/0.48  % (12818)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2))),
% 0.19/0.48    inference(flattening,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0)) | v1_xboole_0(X2))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).
% 0.19/0.48  fof(f147,plain,(
% 0.19/0.48    ~v1_xboole_0(k1_xboole_0) | spl3_16),
% 0.19/0.48    inference(avatar_component_clause,[],[f145])).
% 0.19/0.48  fof(f145,plain,(
% 0.19/0.48    spl3_16 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.48    inference(equality_resolution,[],[f29])).
% 0.19/0.48  fof(f29,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.48    inference(cnf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.48  fof(f68,plain,(
% 0.19/0.48    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_6),
% 0.19/0.48    inference(avatar_component_clause,[],[f66])).
% 0.19/0.48  fof(f66,plain,(
% 0.19/0.48    spl3_6 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.48  fof(f148,plain,(
% 0.19/0.48    ~spl3_16 | spl3_1 | ~spl3_15),
% 0.19/0.48    inference(avatar_split_clause,[],[f138,f134,f41,f145])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    spl3_1 <=> v1_xboole_0(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.48  fof(f134,plain,(
% 0.19/0.48    spl3_15 <=> k1_xboole_0 = sK0),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.19/0.48  fof(f138,plain,(
% 0.19/0.48    ~v1_xboole_0(k1_xboole_0) | (spl3_1 | ~spl3_15)),
% 0.19/0.48    inference(backward_demodulation,[],[f43,f136])).
% 0.19/0.48  fof(f136,plain,(
% 0.19/0.48    k1_xboole_0 = sK0 | ~spl3_15),
% 0.19/0.48    inference(avatar_component_clause,[],[f134])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ~v1_xboole_0(sK0) | spl3_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f41])).
% 0.19/0.48  fof(f137,plain,(
% 0.19/0.48    spl3_15 | spl3_2 | ~spl3_3 | ~spl3_11),
% 0.19/0.48    inference(avatar_split_clause,[],[f130,f105,f51,f46,f134])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    spl3_2 <=> sK0 = sK1),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.48  fof(f51,plain,(
% 0.19/0.48    spl3_3 <=> r1_tarski(sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.48  fof(f105,plain,(
% 0.19/0.48    spl3_11 <=> sK1 = k1_tarski(sK2(sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.48  fof(f130,plain,(
% 0.19/0.48    sK0 = sK1 | k1_xboole_0 = sK0 | (~spl3_3 | ~spl3_11)),
% 0.19/0.48    inference(resolution,[],[f129,f53])).
% 0.19/0.48  fof(f53,plain,(
% 0.19/0.48    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.19/0.48    inference(avatar_component_clause,[],[f51])).
% 0.19/0.48  fof(f129,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) ) | ~spl3_11),
% 0.19/0.48    inference(superposition,[],[f31,f107])).
% 0.19/0.48  fof(f107,plain,(
% 0.19/0.48    sK1 = k1_tarski(sK2(sK1)) | ~spl3_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f105])).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.19/0.48  fof(f108,plain,(
% 0.19/0.48    ~spl3_4 | spl3_5 | spl3_11 | spl3_5 | ~spl3_8),
% 0.19/0.48    inference(avatar_split_clause,[],[f103,f86,f61,f105,f61,f56])).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    spl3_4 <=> v1_zfmisc_1(sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    spl3_5 <=> v1_xboole_0(sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.48  fof(f86,plain,(
% 0.19/0.48    spl3_8 <=> sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.48  fof(f103,plain,(
% 0.19/0.48    sK1 = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1) | (spl3_5 | ~spl3_8)),
% 0.19/0.48    inference(forward_demodulation,[],[f102,f88])).
% 0.19/0.48  fof(f88,plain,(
% 0.19/0.48    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~spl3_8),
% 0.19/0.48    inference(avatar_component_clause,[],[f86])).
% 0.19/0.48  fof(f102,plain,(
% 0.19/0.48    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1) | spl3_5),
% 0.19/0.48    inference(resolution,[],[f91,f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.19/0.48  fof(f91,plain,(
% 0.19/0.48    ( ! [X1] : (~m1_subset_1(X1,sK1) | k1_tarski(X1) = k6_domain_1(sK1,X1)) ) | spl3_5),
% 0.19/0.48    inference(resolution,[],[f27,f63])).
% 0.19/0.48  fof(f63,plain,(
% 0.19/0.48    ~v1_xboole_0(sK1) | spl3_5),
% 0.19/0.48    inference(avatar_component_clause,[],[f61])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k1_tarski(X1) = k6_domain_1(X0,X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.48    inference(flattening,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.19/0.48  fof(f89,plain,(
% 0.19/0.48    spl3_5 | spl3_8 | ~spl3_4),
% 0.19/0.48    inference(avatar_split_clause,[],[f84,f56,f86,f61])).
% 0.19/0.48  fof(f84,plain,(
% 0.19/0.48    sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1) | ~spl3_4),
% 0.19/0.48    inference(resolution,[],[f25,f58])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    v1_zfmisc_1(sK1) | ~spl3_4),
% 0.19/0.48    inference(avatar_component_clause,[],[f56])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f12])).
% 0.19/0.48  fof(f69,plain,(
% 0.19/0.48    spl3_6),
% 0.19/0.48    inference(avatar_split_clause,[],[f35,f66])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.19/0.48    inference(equality_resolution,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.19/0.48    inference(cnf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.19/0.48  fof(f64,plain,(
% 0.19/0.48    ~spl3_5),
% 0.19/0.48    inference(avatar_split_clause,[],[f17,f61])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ~v1_xboole_0(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.19/0.48    inference(flattening,[],[f9])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,negated_conjecture,(
% 0.19/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.19/0.48    inference(negated_conjecture,[],[f7])).
% 0.19/0.48  fof(f7,conjecture,(
% 0.19/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.19/0.48  fof(f59,plain,(
% 0.19/0.48    spl3_4),
% 0.19/0.48    inference(avatar_split_clause,[],[f18,f56])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    v1_zfmisc_1(sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    spl3_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f19,f51])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    r1_tarski(sK0,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f49,plain,(
% 0.19/0.48    ~spl3_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f20,f46])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    sK0 != sK1),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ~spl3_1),
% 0.19/0.48    inference(avatar_split_clause,[],[f21,f41])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ~v1_xboole_0(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f10])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (12813)------------------------------
% 0.19/0.48  % (12813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (12813)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (12813)Memory used [KB]: 6140
% 0.19/0.48  % (12813)Time elapsed: 0.073 s
% 0.19/0.48  % (12813)------------------------------
% 0.19/0.48  % (12813)------------------------------
% 0.19/0.48  % (12797)Success in time 0.137 s
%------------------------------------------------------------------------------
