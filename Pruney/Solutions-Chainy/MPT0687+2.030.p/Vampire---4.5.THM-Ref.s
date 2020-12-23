%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  91 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  133 ( 283 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f32,f93,f105])).

fof(f105,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f101,f26])).

fof(f26,plain,
    ( r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> r2_hidden(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f101,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f100,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | ~ r2_hidden(X4,X6)
      | ~ r1_xboole_0(X6,k1_tarski(X4)) ) ),
    inference(resolution,[],[f56,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f43,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f40,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f39,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(X1,X1) ) ),
    inference(factoring,[],[f16])).

fof(f100,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f99,f15])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k2_relat_1(X1))
        <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f99,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f98])).

fof(f98,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f20,f29])).

fof(f29,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_2
  <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k10_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f93,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f91,f30])).

fof(f30,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f91,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f89,f15])).

fof(f89,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | spl3_1 ),
    inference(resolution,[],[f87,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f87,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl3_1 ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0))
    | spl3_1 ),
    inference(resolution,[],[f81,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(k2_relat_1(sK1),X0),k1_tarski(sK0))
        | r1_xboole_0(k2_relat_1(sK1),X0) )
    | spl3_1 ),
    inference(resolution,[],[f75,f17])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | ~ r2_hidden(X0,k1_tarski(sK0)) )
    | spl3_1 ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,
    ( ~ r2_hidden(sK0,k2_relat_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k1_tarski(X0)) ) ),
    inference(resolution,[],[f16,f21])).

fof(f32,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f14,f28,f24])).

fof(f14,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f13,f28,f24])).

fof(f13,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0))
    | r2_hidden(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (9912)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.41  % (9916)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (9917)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (9912)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f31,f32,f93,f105])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    ~spl3_1 | ~spl3_2),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f104])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    $false | (~spl3_1 | ~spl3_2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f101,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    r2_hidden(sK0,k2_relat_1(sK1)) | ~spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    spl3_1 <=> r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    ~r2_hidden(sK0,k2_relat_1(sK1)) | ~spl3_2),
% 0.21/0.42    inference(resolution,[],[f100,f67])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(condensation,[],[f64])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X6,X4,X5] : (~r2_hidden(X4,X5) | ~r2_hidden(X4,X6) | ~r1_xboole_0(X6,k1_tarski(X4))) )),
% 0.21/0.42    inference(resolution,[],[f56,f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(rectify,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(X0,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(resolution,[],[f43,f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(resolution,[],[f40,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X0)) )),
% 0.21/0.42    inference(resolution,[],[f39,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(X1,X1)) )),
% 0.21/0.42    inference(factoring,[],[f16])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~spl3_2),
% 0.21/0.42    inference(subsumption_resolution,[],[f99,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    v1_relat_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1] : ((r2_hidden(X0,k2_relat_1(X1)) <~> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))) & v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k2_relat_1(X1)) <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).
% 0.21/0.42  fof(f99,plain,(
% 0.21/0.42    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f98])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | ~v1_relat_1(sK1) | ~spl3_2),
% 0.21/0.42    inference(superposition,[],[f20,f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl3_2 <=> k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k10_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : ((k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => (k10_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl3_1 | spl3_2),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    $false | (spl3_1 | spl3_2)),
% 0.21/0.42    inference(subsumption_resolution,[],[f91,f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f28])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | spl3_1),
% 0.21/0.42    inference(subsumption_resolution,[],[f89,f15])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    ~v1_relat_1(sK1) | k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | spl3_1),
% 0.21/0.42    inference(resolution,[],[f87,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k10_relat_1(X1,X0) = k1_xboole_0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl3_1),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f84])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | r1_xboole_0(k2_relat_1(sK1),k1_tarski(sK0)) | spl3_1),
% 0.21/0.42    inference(resolution,[],[f81,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(sK2(k2_relat_1(sK1),X0),k1_tarski(sK0)) | r1_xboole_0(k2_relat_1(sK1),X0)) ) | spl3_1),
% 0.21/0.42    inference(resolution,[],[f75,f17])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,k1_tarski(sK0))) ) | spl3_1),
% 0.21/0.42    inference(resolution,[],[f38,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ~r2_hidden(sK0,k2_relat_1(sK1)) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f24])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k1_tarski(X0))) )),
% 0.21/0.42    inference(resolution,[],[f16,f21])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ~spl3_1 | spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f28,f24])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k1_xboole_0 = k10_relat_1(sK1,k1_tarski(sK0)) | ~r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl3_1 | ~spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f13,f28,f24])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(sK1,k1_tarski(sK0)) | r2_hidden(sK0,k2_relat_1(sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (9912)------------------------------
% 0.21/0.42  % (9912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (9912)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (9912)Memory used [KB]: 10618
% 0.21/0.42  % (9912)Time elapsed: 0.007 s
% 0.21/0.42  % (9912)------------------------------
% 0.21/0.42  % (9912)------------------------------
% 0.21/0.42  % (9911)Success in time 0.063 s
%------------------------------------------------------------------------------
