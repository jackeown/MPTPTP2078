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
% DateTime   : Thu Dec  3 12:55:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 148 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   20
%              Number of atoms          :  174 ( 342 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f957,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f573,f640,f956])).

fof(f956,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f955])).

fof(f955,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f954,f24])).

fof(f24,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

fof(f954,plain,
    ( v3_ordinal1(k3_tarski(sK0))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f952,f43])).

fof(f43,plain,(
    v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0))) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f42,plain,(
    v3_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f952,plain,
    ( ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0)))
    | v3_ordinal1(k3_tarski(sK0))
    | ~ spl4_1 ),
    inference(resolution,[],[f948,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f948,plain,
    ( r2_hidden(k3_tarski(sK0),k1_ordinal1(k1_ordinal1(sK0)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f944,f43])).

fof(f944,plain,
    ( ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0)))
    | r2_hidden(k3_tarski(sK0),k1_ordinal1(k1_ordinal1(sK0)))
    | ~ spl4_1 ),
    inference(resolution,[],[f907,f25])).

fof(f25,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f907,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_ordinal1(sK0),X2)
        | ~ v3_ordinal1(X2)
        | r2_hidden(k3_tarski(sK0),X2) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f906,f568])).

fof(f568,plain,
    ( v1_ordinal1(k3_tarski(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl4_1
  <=> v1_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f906,plain,(
    ! [X2] :
      ( ~ v3_ordinal1(X2)
      | ~ v1_ordinal1(k3_tarski(sK0))
      | ~ r2_hidden(k1_ordinal1(sK0),X2)
      | r2_hidden(k3_tarski(sK0),X2) ) ),
    inference(resolution,[],[f901,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X2)
      | ~ v1_ordinal1(X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(subsumption_resolution,[],[f26,f33])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X0,X2)
              | ~ r2_hidden(X1,X2)
              | ~ r1_tarski(X0,X1)
              | ~ v3_ordinal1(X2) )
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ! [X2] :
              ( v3_ordinal1(X2)
             => ( ( r2_hidden(X1,X2)
                  & r1_tarski(X0,X1) )
               => r2_hidden(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

fof(f901,plain,(
    r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0)) ),
    inference(duplicate_literal_removal,[],[f896])).

fof(f896,plain,
    ( r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0))
    | r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0)) ),
    inference(resolution,[],[f878,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f878,plain,(
    ! [X2] :
      ( r1_tarski(sK2(sK0,X2),k1_ordinal1(sK0))
      | r1_tarski(k3_tarski(sK0),X2) ) ),
    inference(subsumption_resolution,[],[f875,f45])).

fof(f45,plain,(
    v1_ordinal1(k1_ordinal1(sK0)) ),
    inference(resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f875,plain,(
    ! [X2] :
      ( r1_tarski(k3_tarski(sK0),X2)
      | r1_tarski(sK2(sK0,X2),k1_ordinal1(sK0))
      | ~ v1_ordinal1(k1_ordinal1(sK0)) ) ),
    inference(resolution,[],[f668,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f668,plain,(
    ! [X21] :
      ( r2_hidden(sK2(sK0,X21),k1_ordinal1(sK0))
      | r1_tarski(k3_tarski(sK0),X21) ) ),
    inference(resolution,[],[f155,f161])).

fof(f161,plain,(
    r1_tarski(sK0,k1_ordinal1(sK0)) ),
    inference(resolution,[],[f83,f45])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_ordinal1(k1_ordinal1(X0))
      | r1_tarski(X0,k1_ordinal1(X0)) ) ),
    inference(resolution,[],[f30,f25])).

fof(f155,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,X6)
      | r2_hidden(sK2(X4,X5),X6)
      | r1_tarski(k3_tarski(X4),X5) ) ),
    inference(resolution,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f640,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f635,f570,f566])).

fof(f570,plain,
    ( spl4_2
  <=> r2_hidden(sK1(k3_tarski(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f635,plain,
    ( v1_ordinal1(k3_tarski(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f576,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f576,plain,
    ( r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f572,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f572,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f570])).

fof(f573,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f563,f570,f566])).

fof(f563,plain,
    ( r2_hidden(sK1(k3_tarski(sK0)),sK0)
    | v1_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f561,f154])).

fof(f154,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r2_hidden(sK1(X2),X3)
      | v1_ordinal1(X2) ) ),
    inference(resolution,[],[f37,f31])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f561,plain,(
    r1_tarski(k3_tarski(sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f558])).

fof(f558,plain,
    ( r1_tarski(k3_tarski(sK0),sK0)
    | r1_tarski(k3_tarski(sK0),sK0) ),
    inference(resolution,[],[f554,f36])).

fof(f554,plain,(
    ! [X35] :
      ( r1_tarski(sK2(sK0,X35),sK0)
      | r1_tarski(k3_tarski(sK0),X35) ) ),
    inference(resolution,[],[f130,f40])).

fof(f40,plain,(
    v1_ordinal1(sK0) ),
    inference(resolution,[],[f28,f23])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(X0)
      | r1_tarski(sK2(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(resolution,[],[f35,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (1776)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.44  % (1767)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.45  % (1775)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.45  % (1766)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.45  % (1767)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.46  % (1774)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.46  % (1765)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f957,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f573,f640,f956])).
% 0.22/0.47  fof(f956,plain,(
% 0.22/0.47    ~spl4_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f955])).
% 0.22/0.47  fof(f955,plain,(
% 0.22/0.47    $false | ~spl4_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f954,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ~v3_ordinal1(k3_tarski(sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.22/0.47    inference(negated_conjecture,[],[f10])).
% 0.22/0.47  fof(f10,conjecture,(
% 0.22/0.47    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).
% 0.22/0.47  fof(f954,plain,(
% 0.22/0.47    v3_ordinal1(k3_tarski(sK0)) | ~spl4_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f952,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0)))),
% 0.22/0.47    inference(resolution,[],[f42,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    v3_ordinal1(k1_ordinal1(sK0))),
% 0.22/0.47    inference(resolution,[],[f27,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    v3_ordinal1(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f952,plain,(
% 0.22/0.47    ~v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0))) | v3_ordinal1(k3_tarski(sK0)) | ~spl4_1),
% 0.22/0.47    inference(resolution,[],[f948,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | v3_ordinal1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.22/0.47    inference(flattening,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.22/0.47  fof(f948,plain,(
% 0.22/0.47    r2_hidden(k3_tarski(sK0),k1_ordinal1(k1_ordinal1(sK0))) | ~spl4_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f944,f43])).
% 0.22/0.47  fof(f944,plain,(
% 0.22/0.47    ~v3_ordinal1(k1_ordinal1(k1_ordinal1(sK0))) | r2_hidden(k3_tarski(sK0),k1_ordinal1(k1_ordinal1(sK0))) | ~spl4_1),
% 0.22/0.47    inference(resolution,[],[f907,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.22/0.47  fof(f907,plain,(
% 0.22/0.47    ( ! [X2] : (~r2_hidden(k1_ordinal1(sK0),X2) | ~v3_ordinal1(X2) | r2_hidden(k3_tarski(sK0),X2)) ) | ~spl4_1),
% 0.22/0.47    inference(subsumption_resolution,[],[f906,f568])).
% 0.22/0.47  fof(f568,plain,(
% 0.22/0.47    v1_ordinal1(k3_tarski(sK0)) | ~spl4_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f566])).
% 0.22/0.47  fof(f566,plain,(
% 0.22/0.47    spl4_1 <=> v1_ordinal1(k3_tarski(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.47  fof(f906,plain,(
% 0.22/0.47    ( ! [X2] : (~v3_ordinal1(X2) | ~v1_ordinal1(k3_tarski(sK0)) | ~r2_hidden(k1_ordinal1(sK0),X2) | r2_hidden(k3_tarski(sK0),X2)) )),
% 0.22/0.47    inference(resolution,[],[f901,f186])).
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v3_ordinal1(X2) | ~v1_ordinal1(X0) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f26,f33])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~v1_ordinal1(X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X2) | ~r1_tarski(X0,X1) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X0,X2) | (~r2_hidden(X1,X2) | ~r1_tarski(X0,X1))) | ~v3_ordinal1(X2)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ! [X2] : (v3_ordinal1(X2) => ((r2_hidden(X1,X2) & r1_tarski(X0,X1)) => r2_hidden(X0,X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).
% 0.22/0.47  fof(f901,plain,(
% 0.22/0.47    r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0))),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f896])).
% 0.22/0.47  fof(f896,plain,(
% 0.22/0.47    r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0)) | r1_tarski(k3_tarski(sK0),k1_ordinal1(sK0))),
% 0.22/0.47    inference(resolution,[],[f878,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(sK2(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.22/0.47  fof(f878,plain,(
% 0.22/0.47    ( ! [X2] : (r1_tarski(sK2(sK0,X2),k1_ordinal1(sK0)) | r1_tarski(k3_tarski(sK0),X2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f875,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    v1_ordinal1(k1_ordinal1(sK0))),
% 0.22/0.47    inference(resolution,[],[f42,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.22/0.47  fof(f875,plain,(
% 0.22/0.47    ( ! [X2] : (r1_tarski(k3_tarski(sK0),X2) | r1_tarski(sK2(sK0,X2),k1_ordinal1(sK0)) | ~v1_ordinal1(k1_ordinal1(sK0))) )),
% 0.22/0.47    inference(resolution,[],[f668,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.22/0.47  fof(f668,plain,(
% 0.22/0.47    ( ! [X21] : (r2_hidden(sK2(sK0,X21),k1_ordinal1(sK0)) | r1_tarski(k3_tarski(sK0),X21)) )),
% 0.22/0.47    inference(resolution,[],[f155,f161])).
% 0.22/0.47  fof(f161,plain,(
% 0.22/0.47    r1_tarski(sK0,k1_ordinal1(sK0))),
% 0.22/0.47    inference(resolution,[],[f83,f45])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_ordinal1(k1_ordinal1(X0)) | r1_tarski(X0,k1_ordinal1(X0))) )),
% 0.22/0.47    inference(resolution,[],[f30,f25])).
% 0.22/0.47  fof(f155,plain,(
% 0.22/0.47    ( ! [X6,X4,X5] : (~r1_tarski(X4,X6) | r2_hidden(sK2(X4,X5),X6) | r1_tarski(k3_tarski(X4),X5)) )),
% 0.22/0.47    inference(resolution,[],[f37,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.47  fof(f640,plain,(
% 0.22/0.47    spl4_1 | ~spl4_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f635,f570,f566])).
% 0.22/0.47  fof(f570,plain,(
% 0.22/0.47    spl4_2 <=> r2_hidden(sK1(k3_tarski(sK0)),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.47  fof(f635,plain,(
% 0.22/0.47    v1_ordinal1(k3_tarski(sK0)) | ~spl4_2),
% 0.22/0.47    inference(resolution,[],[f576,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(sK1(X0),X0) | v1_ordinal1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f576,plain,(
% 0.22/0.47    r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) | ~spl4_2),
% 0.22/0.47    inference(resolution,[],[f572,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.47  fof(f572,plain,(
% 0.22/0.47    r2_hidden(sK1(k3_tarski(sK0)),sK0) | ~spl4_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f570])).
% 0.22/0.47  fof(f573,plain,(
% 0.22/0.47    spl4_1 | spl4_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f563,f570,f566])).
% 0.22/0.47  fof(f563,plain,(
% 0.22/0.47    r2_hidden(sK1(k3_tarski(sK0)),sK0) | v1_ordinal1(k3_tarski(sK0))),
% 0.22/0.47    inference(resolution,[],[f561,f154])).
% 0.22/0.47  fof(f154,plain,(
% 0.22/0.47    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r2_hidden(sK1(X2),X3) | v1_ordinal1(X2)) )),
% 0.22/0.47    inference(resolution,[],[f37,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_ordinal1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f561,plain,(
% 0.22/0.47    r1_tarski(k3_tarski(sK0),sK0)),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f558])).
% 0.22/0.47  fof(f558,plain,(
% 0.22/0.47    r1_tarski(k3_tarski(sK0),sK0) | r1_tarski(k3_tarski(sK0),sK0)),
% 0.22/0.47    inference(resolution,[],[f554,f36])).
% 0.22/0.47  fof(f554,plain,(
% 0.22/0.47    ( ! [X35] : (r1_tarski(sK2(sK0,X35),sK0) | r1_tarski(k3_tarski(sK0),X35)) )),
% 0.22/0.47    inference(resolution,[],[f130,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    v1_ordinal1(sK0)),
% 0.22/0.47    inference(resolution,[],[f28,f23])).
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_ordinal1(X0) | r1_tarski(sK2(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.22/0.47    inference(resolution,[],[f35,f30])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (1767)------------------------------
% 0.22/0.47  % (1767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (1767)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (1767)Memory used [KB]: 5628
% 0.22/0.47  % (1767)Time elapsed: 0.055 s
% 0.22/0.47  % (1767)------------------------------
% 0.22/0.47  % (1767)------------------------------
% 0.22/0.47  % (1760)Success in time 0.108 s
%------------------------------------------------------------------------------
