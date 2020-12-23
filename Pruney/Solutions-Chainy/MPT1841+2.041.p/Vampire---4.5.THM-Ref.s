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
% DateTime   : Thu Dec  3 13:20:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 139 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  221 ( 383 expanded)
%              Number of equality atoms :   27 (  33 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f339,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f204,f211,f213,f220,f325,f327,f338])).

fof(f338,plain,(
    ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f28,f64,f33,f324,f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | v1_subset_1(X2,X1)
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | v1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_xboole_0(X1)
          | v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_subset_1(X1,X0)
           => ~ v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

fof(f324,plain,
    ( v1_xboole_0(sK2(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl4_7
  <=> v1_xboole_0(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f33,plain,(
    ! [X0] : ~ v1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f64,plain,(
    ! [X0] : r1_tarski(sK2(X0),X0) ),
    inference(resolution,[],[f41,f32])).

fof(f32,plain,(
    ! [X0] : m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f327,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f28,f191])).

fof(f191,plain,
    ( v1_xboole_0(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl4_2
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f325,plain,
    ( spl4_2
    | spl4_7
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f320,f201,f197,f322,f189])).

fof(f197,plain,
    ( spl4_4
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f201,plain,
    ( spl4_5
  <=> v1_subset_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f320,plain,
    ( ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK2(sK0))
    | v1_xboole_0(sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f203,f91])).

fof(f91,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(sK2(X1))
      | v1_xboole_0(X1) ) ),
    inference(superposition,[],[f33,f86])).

fof(f86,plain,(
    ! [X1] :
      ( sK2(X1) = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(sK2(X1))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f31,f64])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f203,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f201])).

fof(f220,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f28,f25,f57,f195,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_domain_1(X1,X0),X2)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f111,f69])).

fof(f69,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ v1_xboole_0(X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f48,f40])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f111,plain,(
    ! [X8,X9] :
      ( r2_hidden(X8,k6_domain_1(X9,X8))
      | ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9) ) ),
    inference(superposition,[],[f62,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f62,plain,(
    ! [X3,X1] : r2_hidden(X3,k1_enumset1(X3,X3,X1)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f34])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f195,plain,
    ( v1_xboole_0(k6_domain_1(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl4_3
  <=> v1_xboole_0(k6_domain_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
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

fof(f25,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f213,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f27,f199])).

fof(f199,plain,
    ( ~ v1_zfmisc_1(sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f197])).

fof(f27,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f211,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f25,f187])).

fof(f187,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl4_1
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f204,plain,
    ( ~ spl4_1
    | spl4_2
    | spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f165,f201,f197,f193,f189,f185])).

fof(f165,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(k6_domain_1(sK0,sK1))
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(superposition,[],[f26,f88])).

fof(f88,plain,(
    ! [X2,X3] :
      ( k6_domain_1(X2,X3) = X2
      | ~ v1_zfmisc_1(X2)
      | v1_xboole_0(k6_domain_1(X2,X3))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X2,X3] :
      ( v1_xboole_0(X2)
      | ~ v1_zfmisc_1(X2)
      | v1_xboole_0(k6_domain_1(X2,X3))
      | k6_domain_1(X2,X3) = X2
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,X2) ) ),
    inference(resolution,[],[f31,f80])).

fof(f80,plain,(
    ! [X6,X5] :
      ( r1_tarski(k6_domain_1(X6,X5),X6)
      | v1_xboole_0(X6)
      | ~ m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f36,f41])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f26,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:02:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (28560)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (28552)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (28560)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (28559)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f204,f211,f213,f220,f325,f327,f338])).
% 0.21/0.54  fof(f338,plain,(
% 0.21/0.54    ~spl4_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f331])).
% 0.21/0.54  fof(f331,plain,(
% 0.21/0.54    $false | ~spl4_7),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f28,f64,f33,f324,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~r1_tarski(X2,X1) | v1_subset_1(X2,X1) | ~v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 0.21/0.54    inference(resolution,[],[f30,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0) | v1_subset_1(X1,X0) | ~v1_xboole_0(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (~v1_xboole_0(X1) | v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((~v1_xboole_0(X1) | v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_subset_1(X1,X0) => ~v1_xboole_0(X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).
% 0.21/0.54  fof(f324,plain,(
% 0.21/0.54    v1_xboole_0(sK2(sK0)) | ~spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f322])).
% 0.21/0.54  fof(f322,plain,(
% 0.21/0.54    spl4_7 <=> v1_xboole_0(sK2(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_subset_1(sK2(X0),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK2(X0),X0)) )),
% 0.21/0.54    inference(resolution,[],[f41,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ~v1_xboole_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.54  fof(f327,plain,(
% 0.21/0.54    ~spl4_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f326])).
% 0.21/0.54  fof(f326,plain,(
% 0.21/0.54    $false | ~spl4_2),
% 0.21/0.54    inference(subsumption_resolution,[],[f28,f191])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    v1_xboole_0(sK0) | ~spl4_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f189])).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    spl4_2 <=> v1_xboole_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f325,plain,(
% 0.21/0.54    spl4_2 | spl4_7 | ~spl4_4 | ~spl4_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f320,f201,f197,f322,f189])).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    spl4_4 <=> v1_zfmisc_1(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f201,plain,(
% 0.21/0.54    spl4_5 <=> v1_subset_1(sK0,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    ~v1_zfmisc_1(sK0) | v1_xboole_0(sK2(sK0)) | v1_xboole_0(sK0) | ~spl4_5),
% 0.21/0.54    inference(resolution,[],[f203,f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X1] : (~v1_subset_1(X1,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(sK2(X1)) | v1_xboole_0(X1)) )),
% 0.21/0.54    inference(superposition,[],[f33,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X1] : (sK2(X1) = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(sK2(X1)) | v1_xboole_0(X1)) )),
% 0.21/0.54    inference(resolution,[],[f31,f64])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X0) | X0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    v1_subset_1(sK0,sK0) | ~spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f201])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    ~spl4_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f215])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    $false | ~spl4_3),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f28,f25,f57,f195,f118])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k6_domain_1(X1,X0),X2) | v1_xboole_0(X1) | ~v1_xboole_0(X2) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f111,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (~r2_hidden(X2,X3) | ~v1_xboole_0(X4) | ~r1_tarski(X3,X4)) )),
% 0.21/0.54    inference(resolution,[],[f48,f40])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X8,X9] : (r2_hidden(X8,k6_domain_1(X9,X8)) | ~m1_subset_1(X8,X9) | v1_xboole_0(X9)) )),
% 0.21/0.54    inference(superposition,[],[f62,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f35,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f29,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X3,X1] : (r2_hidden(X3,k1_enumset1(X3,X3,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_enumset1(X3,X3,X1) != X2) )),
% 0.21/0.54    inference(equality_resolution,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f46,f34])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    v1_xboole_0(k6_domain_1(sK0,sK1)) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f193])).
% 0.21/0.54  fof(f193,plain,(
% 0.21/0.54    spl4_3 <=> v1_xboole_0(k6_domain_1(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f213,plain,(
% 0.21/0.54    spl4_4),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f212])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    $false | spl4_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f27,f199])).
% 0.21/0.54  fof(f199,plain,(
% 0.21/0.54    ~v1_zfmisc_1(sK0) | spl4_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f197])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    v1_zfmisc_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f211,plain,(
% 0.21/0.54    spl4_1),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f210])).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    $false | spl4_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f25,f187])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,sK0) | spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f185])).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    spl4_1 <=> m1_subset_1(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    ~spl4_1 | spl4_2 | spl4_3 | ~spl4_4 | spl4_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f165,f201,f197,f193,f189,f185])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    v1_subset_1(sK0,sK0) | ~v1_zfmisc_1(sK0) | v1_xboole_0(k6_domain_1(sK0,sK1)) | v1_xboole_0(sK0) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.54    inference(superposition,[],[f26,f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k6_domain_1(X2,X3) = X2 | ~v1_zfmisc_1(X2) | v1_xboole_0(k6_domain_1(X2,X3)) | v1_xboole_0(X2) | ~m1_subset_1(X3,X2)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X2,X3] : (v1_xboole_0(X2) | ~v1_zfmisc_1(X2) | v1_xboole_0(k6_domain_1(X2,X3)) | k6_domain_1(X2,X3) = X2 | v1_xboole_0(X2) | ~m1_subset_1(X3,X2)) )),
% 0.21/0.54    inference(resolution,[],[f31,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X6,X5] : (r1_tarski(k6_domain_1(X6,X5),X6) | v1_xboole_0(X6) | ~m1_subset_1(X5,X6)) )),
% 0.21/0.54    inference(resolution,[],[f36,f41])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (28560)------------------------------
% 0.21/0.54  % (28560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (28560)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (28560)Memory used [KB]: 6268
% 0.21/0.54  % (28560)Time elapsed: 0.083 s
% 0.21/0.54  % (28560)------------------------------
% 0.21/0.54  % (28560)------------------------------
% 0.21/0.54  % (28567)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (28546)Success in time 0.187 s
%------------------------------------------------------------------------------
