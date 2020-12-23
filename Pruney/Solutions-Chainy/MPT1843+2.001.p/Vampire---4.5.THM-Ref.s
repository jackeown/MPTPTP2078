%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 139 expanded)
%              Number of leaves         :   17 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  205 ( 503 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f68,f70,f100,f106,f108,f110,f113])).

fof(f113,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f57,f111])).

fof(f111,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(resolution,[],[f99,f67])).

fof(f67,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_4
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f99,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(k1_tarski(X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_subset_1(k1_tarski(X5),u1_struct_0(sK0)) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl2_8
  <=> ! [X5] :
        ( ~ m1_subset_1(k1_tarski(X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_subset_1(k1_tarski(X5),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f57,plain,
    ( v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | spl2_1 ),
    inference(backward_demodulation,[],[f31,f56])).

fof(f56,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | spl2_1 ),
    inference(resolution,[],[f55,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( v7_struct_0(sK0)
    & v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v7_struct_0(X0)
            & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v7_struct_0(sK0)
          & v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( v7_struct_0(sK0)
        & v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( v7_struct_0(sK0)
      & v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ ( v7_struct_0(X0)
                & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f55,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k6_domain_1(u1_struct_0(sK0),X5) = k1_tarski(X5) )
    | spl2_1 ),
    inference(resolution,[],[f40,f47])).

fof(f47,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f31,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl2_9 ),
    inference(subsumption_resolution,[],[f32,f105])).

fof(f105,plain,
    ( ~ v7_struct_0(sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_9
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f32,plain,(
    v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f108,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f29,f51])).

fof(f51,plain,
    ( ~ l1_struct_0(sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f29,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,
    ( ~ spl2_9
    | ~ spl2_2
    | spl2_6 ),
    inference(avatar_split_clause,[],[f101,f84,f49,f103])).

fof(f84,plain,
    ( spl2_6
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f101,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v7_struct_0(sK0)
    | spl2_6 ),
    inference(resolution,[],[f86,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f86,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f100,plain,
    ( ~ spl2_6
    | spl2_8
    | spl2_1 ),
    inference(avatar_split_clause,[],[f96,f45,f98,f84])).

fof(f96,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(k1_tarski(X5),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_zfmisc_1(u1_struct_0(sK0))
        | ~ v1_subset_1(k1_tarski(X5),u1_struct_0(sK0)) )
    | spl2_1 ),
    inference(resolution,[],[f74,f47])).

fof(f74,plain,(
    ! [X4,X3] :
      ( v1_xboole_0(X4)
      | ~ m1_subset_1(k1_tarski(X3),k1_zfmisc_1(X4))
      | ~ v1_zfmisc_1(X4)
      | ~ v1_subset_1(k1_tarski(X3),X4) ) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(superposition,[],[f38,f33])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f70,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f30,f63])).

fof(f63,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f68,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f59,f45,f65,f61,f45])).

fof(f59,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl2_1 ),
    inference(superposition,[],[f41,f56])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f52,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f43,f49,f45])).

fof(f43,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:57:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (24355)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.44  % (24355)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % (24352)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f114,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(avatar_sat_refutation,[],[f52,f68,f70,f100,f106,f108,f110,f113])).
% 0.20/0.44  fof(f113,plain,(
% 0.20/0.44    spl2_1 | ~spl2_4 | ~spl2_8),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.44  fof(f112,plain,(
% 0.20/0.44    $false | (spl2_1 | ~spl2_4 | ~spl2_8)),
% 0.20/0.44    inference(subsumption_resolution,[],[f57,f111])).
% 0.20/0.44  fof(f111,plain,(
% 0.20/0.44    ~v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | (~spl2_4 | ~spl2_8)),
% 0.20/0.44    inference(resolution,[],[f99,f67])).
% 0.20/0.44  fof(f67,plain,(
% 0.20/0.44    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f65])).
% 0.20/0.44  fof(f65,plain,(
% 0.20/0.44    spl2_4 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.44  fof(f99,plain,(
% 0.20/0.44    ( ! [X5] : (~m1_subset_1(k1_tarski(X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_subset_1(k1_tarski(X5),u1_struct_0(sK0))) ) | ~spl2_8),
% 0.20/0.44    inference(avatar_component_clause,[],[f98])).
% 0.20/0.44  fof(f98,plain,(
% 0.20/0.44    spl2_8 <=> ! [X5] : (~m1_subset_1(k1_tarski(X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_subset_1(k1_tarski(X5),u1_struct_0(sK0)))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.44  fof(f57,plain,(
% 0.20/0.44    v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) | spl2_1),
% 0.20/0.44    inference(backward_demodulation,[],[f31,f56])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | spl2_1),
% 0.20/0.44    inference(resolution,[],[f55,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.44    inference(cnf_transformation,[],[f27])).
% 0.20/0.44  fof(f27,plain,(
% 0.20/0.44    (v7_struct_0(sK0) & v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f26,f25])).
% 0.20/0.44  fof(f25,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (v7_struct_0(sK0) & v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    ? [X1] : (v7_struct_0(sK0) & v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => (v7_struct_0(sK0) & v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : (v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : ((v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,negated_conjecture,(
% 0.20/0.44    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.44    inference(negated_conjecture,[],[f10])).
% 0.20/0.44  fof(f10,conjecture,(
% 0.20/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.20/0.44  fof(f55,plain,(
% 0.20/0.44    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),X5) = k1_tarski(X5)) ) | spl2_1),
% 0.20/0.44    inference(resolution,[],[f40,f47])).
% 0.20/0.44  fof(f47,plain,(
% 0.20/0.44    ~v1_xboole_0(u1_struct_0(sK0)) | spl2_1),
% 0.20/0.44    inference(avatar_component_clause,[],[f45])).
% 0.20/0.44  fof(f45,plain,(
% 0.20/0.44    spl2_1 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f22])).
% 0.20/0.44  fof(f22,plain,(
% 0.20/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f21])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f8])).
% 0.20/0.44  fof(f8,axiom,(
% 0.20/0.44    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.44  fof(f31,plain,(
% 0.20/0.44    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.44    inference(cnf_transformation,[],[f27])).
% 0.20/0.44  fof(f110,plain,(
% 0.20/0.44    spl2_9),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f109])).
% 0.20/0.44  fof(f109,plain,(
% 0.20/0.44    $false | spl2_9),
% 0.20/0.44    inference(subsumption_resolution,[],[f32,f105])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    ~v7_struct_0(sK0) | spl2_9),
% 0.20/0.44    inference(avatar_component_clause,[],[f103])).
% 0.20/0.44  fof(f103,plain,(
% 0.20/0.44    spl2_9 <=> v7_struct_0(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.44  fof(f32,plain,(
% 0.20/0.44    v7_struct_0(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f27])).
% 0.20/0.44  fof(f108,plain,(
% 0.20/0.44    spl2_2),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.44  fof(f107,plain,(
% 0.20/0.44    $false | spl2_2),
% 0.20/0.44    inference(subsumption_resolution,[],[f29,f51])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    ~l1_struct_0(sK0) | spl2_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f49])).
% 0.20/0.44  fof(f49,plain,(
% 0.20/0.44    spl2_2 <=> l1_struct_0(sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.44  fof(f29,plain,(
% 0.20/0.44    l1_struct_0(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f27])).
% 0.20/0.44  fof(f106,plain,(
% 0.20/0.44    ~spl2_9 | ~spl2_2 | spl2_6),
% 0.20/0.44    inference(avatar_split_clause,[],[f101,f84,f49,f103])).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    spl2_6 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.44  fof(f101,plain,(
% 0.20/0.44    ~l1_struct_0(sK0) | ~v7_struct_0(sK0) | spl2_6),
% 0.20/0.44    inference(resolution,[],[f86,f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f19])).
% 0.20/0.44  fof(f19,plain,(
% 0.20/0.44    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.20/0.44  fof(f86,plain,(
% 0.20/0.44    ~v1_zfmisc_1(u1_struct_0(sK0)) | spl2_6),
% 0.20/0.44    inference(avatar_component_clause,[],[f84])).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    ~spl2_6 | spl2_8 | spl2_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f96,f45,f98,f84])).
% 0.20/0.44  fof(f96,plain,(
% 0.20/0.44    ( ! [X5] : (~m1_subset_1(k1_tarski(X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(u1_struct_0(sK0)) | ~v1_subset_1(k1_tarski(X5),u1_struct_0(sK0))) ) | spl2_1),
% 0.20/0.44    inference(resolution,[],[f74,f47])).
% 0.20/0.44  fof(f74,plain,(
% 0.20/0.44    ( ! [X4,X3] : (v1_xboole_0(X4) | ~m1_subset_1(k1_tarski(X3),k1_zfmisc_1(X4)) | ~v1_zfmisc_1(X4) | ~v1_subset_1(k1_tarski(X3),X4)) )),
% 0.20/0.44    inference(resolution,[],[f36,f42])).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.44    inference(superposition,[],[f38,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.44  fof(f38,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~v1_xboole_0(k2_tarski(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f3])).
% 0.20/0.44  fof(f3,axiom,(
% 0.20/0.44    ! [X0,X1] : ~v1_xboole_0(k2_tarski(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).
% 0.20/0.44  fof(f36,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f18])).
% 0.20/0.44  fof(f18,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,axiom,(
% 0.20/0.44    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.20/0.44  fof(f70,plain,(
% 0.20/0.44    spl2_3),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f69])).
% 0.20/0.44  fof(f69,plain,(
% 0.20/0.44    $false | spl2_3),
% 0.20/0.44    inference(subsumption_resolution,[],[f30,f63])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl2_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f61])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    spl2_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.44  fof(f68,plain,(
% 0.20/0.44    spl2_1 | ~spl2_3 | spl2_4 | spl2_1),
% 0.20/0.44    inference(avatar_split_clause,[],[f59,f45,f65,f61,f45])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl2_1),
% 0.20/0.44    inference(superposition,[],[f41,f56])).
% 0.20/0.44  fof(f41,plain,(
% 0.20/0.44    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.44    inference(flattening,[],[f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.44  fof(f52,plain,(
% 0.20/0.44    ~spl2_1 | ~spl2_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f43,f49,f45])).
% 0.20/0.44  fof(f43,plain,(
% 0.20/0.44    ~l1_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.44    inference(resolution,[],[f35,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ~v2_struct_0(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f27])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (24355)------------------------------
% 0.20/0.44  % (24355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (24355)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (24355)Memory used [KB]: 6140
% 0.20/0.44  % (24355)Time elapsed: 0.041 s
% 0.20/0.44  % (24355)------------------------------
% 0.20/0.44  % (24355)------------------------------
% 0.20/0.45  % (24338)Success in time 0.087 s
%------------------------------------------------------------------------------
