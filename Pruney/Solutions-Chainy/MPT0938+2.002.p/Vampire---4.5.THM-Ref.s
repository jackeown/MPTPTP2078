%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 236 expanded)
%              Number of leaves         :    7 (  55 expanded)
%              Depth                    :   28
%              Number of atoms          :  224 ( 752 expanded)
%              Number of equality atoms :   12 (  81 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f255])).

fof(f255,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f253,f44])).

fof(f44,plain,
    ( ~ v8_relat_2(k1_wellord2(sK0))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl7_1
  <=> v8_relat_2(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f253,plain,(
    ! [X2] : v8_relat_2(k1_wellord2(X2)) ),
    inference(global_subsumption,[],[f250])).

fof(f250,plain,(
    ! [X4] : v8_relat_2(k1_wellord2(X4)) ),
    inference(global_subsumption,[],[f249])).

fof(f249,plain,(
    ! [X2] : v8_relat_2(k1_wellord2(X2)) ),
    inference(global_subsumption,[],[f248])).

fof(f248,plain,(
    ! [X1] : v8_relat_2(k1_wellord2(X1)) ),
    inference(global_subsumption,[],[f17,f247])).

% (6453)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (6446)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f247,plain,(
    ! [X1] :
      ( v8_relat_2(k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,(
    ! [X1] :
      ( v8_relat_2(k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1))
      | v8_relat_2(k1_wellord2(X1)) ) ),
    inference(resolution,[],[f237,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0)
      | ~ v1_relat_1(X0)
      | v8_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( r2_hidden(k4_tarski(X1,X3),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(k4_tarski(X1,X2),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v8_relat_2(X0)
      <=> ! [X1,X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X0)
              & r2_hidden(k4_tarski(X1,X2),X0) )
           => r2_hidden(k4_tarski(X1,X3),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).

fof(f237,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f236])).

fof(f236,plain,(
    ! [X0] :
      ( v8_relat_2(k1_wellord2(X0))
      | r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f226,f87])).

fof(f87,plain,(
    ! [X7] :
      ( r2_hidden(sK3(k1_wellord2(X7)),X7)
      | v8_relat_2(k1_wellord2(X7)) ) ),
    inference(global_subsumption,[],[f17,f86])).

fof(f86,plain,(
    ! [X7] :
      ( r2_hidden(sK3(k1_wellord2(X7)),X7)
      | v8_relat_2(k1_wellord2(X7))
      | ~ v1_relat_1(k1_wellord2(X7)) ) ),
    inference(forward_demodulation,[],[f84,f46])).

fof(f46,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f17,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f84,plain,(
    ! [X7] :
      ( v8_relat_2(k1_wellord2(X7))
      | ~ v1_relat_1(k1_wellord2(X7))
      | r2_hidden(sK3(k1_wellord2(X7)),k3_relat_1(k1_wellord2(X7))) ) ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f20,f17])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | v8_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f226,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0))
      | r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X0] :
      ( v8_relat_2(k1_wellord2(X0))
      | ~ r2_hidden(sK3(k1_wellord2(X0)),X0)
      | r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f219,f74])).

fof(f74,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK1(k1_wellord2(X3)),X2)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(k4_tarski(sK1(k1_wellord2(X3)),X2),k1_wellord2(X3))
      | v8_relat_2(k1_wellord2(X3)) ) ),
    inference(resolution,[],[f48,f63])).

fof(f63,plain,(
    ! [X3] :
      ( r2_hidden(sK1(k1_wellord2(X3)),X3)
      | v8_relat_2(k1_wellord2(X3)) ) ),
    inference(global_subsumption,[],[f17,f62])).

% (6449)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f62,plain,(
    ! [X3] :
      ( r2_hidden(sK1(k1_wellord2(X3)),X3)
      | v8_relat_2(k1_wellord2(X3))
      | ~ v1_relat_1(k1_wellord2(X3)) ) ),
    inference(forward_demodulation,[],[f59,f46])).

fof(f59,plain,(
    ! [X3] :
      ( v8_relat_2(k1_wellord2(X3))
      | ~ v1_relat_1(k1_wellord2(X3))
      | r2_hidden(sK1(k1_wellord2(X3)),k3_relat_1(k1_wellord2(X3))) ) ),
    inference(resolution,[],[f52,f32])).

% (6459)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))),k1_wellord2(X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f19,f17])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | v8_relat_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    inference(global_subsumption,[],[f17,f40])).

fof(f40,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f219,plain,(
    ! [X0] :
      ( r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0] :
      ( r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0))
      | r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) ) ),
    inference(resolution,[],[f197,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f197,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK1(k1_wellord2(X0)),X1),sK3(k1_wellord2(X0)))
      | r1_tarski(sK1(k1_wellord2(X0)),X1)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK1(k1_wellord2(X0)),X1)
      | r2_hidden(sK6(sK1(k1_wellord2(X0)),X1),sK3(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f125,f113])).

fof(f113,plain,(
    ! [X0] :
      ( r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f111,f61])).

fof(f61,plain,(
    ! [X2] :
      ( r2_hidden(sK2(k1_wellord2(X2)),X2)
      | v8_relat_2(k1_wellord2(X2)) ) ),
    inference(global_subsumption,[],[f17,f60])).

% (6440)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f60,plain,(
    ! [X2] :
      ( r2_hidden(sK2(k1_wellord2(X2)),X2)
      | v8_relat_2(k1_wellord2(X2))
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(forward_demodulation,[],[f58,f46])).

fof(f58,plain,(
    ! [X2] :
      ( v8_relat_2(k1_wellord2(X2))
      | ~ v1_relat_1(k1_wellord2(X2))
      | r2_hidden(sK2(k1_wellord2(X2)),k3_relat_1(k1_wellord2(X2))) ) ),
    inference(resolution,[],[f52,f33])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k1_wellord2(X0)),X0)
      | r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( v8_relat_2(k1_wellord2(X0))
      | r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | ~ r2_hidden(sK2(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f80,f87])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0))
      | r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0)))
      | ~ r2_hidden(sK2(k1_wellord2(X0)),X0) ) ),
    inference(resolution,[],[f53,f47])).

fof(f47,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(X2,X0) ) ),
    inference(global_subsumption,[],[f17,f39])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f125,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(sK2(k1_wellord2(X4)),X6)
      | r1_tarski(sK1(k1_wellord2(X4)),X5)
      | r2_hidden(sK6(sK1(k1_wellord2(X4)),X5),X6)
      | v8_relat_2(k1_wellord2(X4)) ) ),
    inference(resolution,[],[f70,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK1(k1_wellord2(X0)),X1),sK2(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0))
      | r1_tarski(sK1(k1_wellord2(X0)),X1) ) ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK6(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0] :
      ( r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0)))
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(global_subsumption,[],[f61,f63,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k1_wellord2(X0)),X0)
      | r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0)))
      | ~ r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v8_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f47,f52])).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f45,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    ~ v8_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : ~ v8_relat_2(k1_wellord2(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : v8_relat_2(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (6441)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (6451)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (6441)Refutation not found, incomplete strategy% (6441)------------------------------
% 0.21/0.51  % (6441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6441)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6441)Memory used [KB]: 10618
% 0.21/0.51  % (6441)Time elapsed: 0.095 s
% 0.21/0.51  % (6441)------------------------------
% 0.21/0.51  % (6441)------------------------------
% 0.21/0.51  % (6445)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (6455)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (6454)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (6444)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (6442)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (6450)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (6447)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (6450)Refutation not found, incomplete strategy% (6450)------------------------------
% 0.21/0.52  % (6450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (6450)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (6450)Memory used [KB]: 10618
% 0.21/0.52  % (6450)Time elapsed: 0.115 s
% 0.21/0.52  % (6450)------------------------------
% 0.21/0.52  % (6450)------------------------------
% 0.21/0.52  % (6458)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (6463)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (6462)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (6443)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (6466)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (6455)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (6461)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (6439)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (6439)Refutation not found, incomplete strategy% (6439)------------------------------
% 0.21/0.53  % (6439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6439)Memory used [KB]: 1663
% 0.21/0.53  % (6439)Time elapsed: 0.116 s
% 0.21/0.53  % (6439)------------------------------
% 0.21/0.53  % (6439)------------------------------
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f45,f255])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    spl7_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f254])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    $false | spl7_1),
% 0.21/0.53    inference(resolution,[],[f253,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ~v8_relat_2(k1_wellord2(sK0)) | spl7_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    spl7_1 <=> v8_relat_2(k1_wellord2(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    ( ! [X2] : (v8_relat_2(k1_wellord2(X2))) )),
% 0.21/0.53    inference(global_subsumption,[],[f250])).
% 0.21/0.54  fof(f250,plain,(
% 0.21/0.54    ( ! [X4] : (v8_relat_2(k1_wellord2(X4))) )),
% 0.21/0.54    inference(global_subsumption,[],[f249])).
% 0.21/0.54  fof(f249,plain,(
% 0.21/0.54    ( ! [X2] : (v8_relat_2(k1_wellord2(X2))) )),
% 0.21/0.54    inference(global_subsumption,[],[f248])).
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    ( ! [X1] : (v8_relat_2(k1_wellord2(X1))) )),
% 0.21/0.54    inference(global_subsumption,[],[f17,f247])).
% 0.21/0.54  % (6453)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (6446)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  fof(f247,plain,(
% 0.21/0.54    ( ! [X1] : (v8_relat_2(k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f241])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ( ! [X1] : (v8_relat_2(k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1)) | v8_relat_2(k1_wellord2(X1))) )),
% 0.21/0.54    inference(resolution,[],[f237,f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(k4_tarski(sK1(X0),sK3(X0)),X0) | ~v1_relat_1(X0) | v8_relat_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ! [X0] : ((v8_relat_2(X0) <=> ! [X1,X2,X3] : (r2_hidden(k4_tarski(X1,X3),X0) | (~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X1,X2),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => (v8_relat_2(X0) <=> ! [X1,X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(k4_tarski(X1,X2),X0)) => r2_hidden(k4_tarski(X1,X3),X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_wellord1)).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f236])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    ( ! [X0] : (v8_relat_2(k1_wellord2(X0)) | r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(resolution,[],[f226,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X7] : (r2_hidden(sK3(k1_wellord2(X7)),X7) | v8_relat_2(k1_wellord2(X7))) )),
% 0.21/0.54    inference(global_subsumption,[],[f17,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X7] : (r2_hidden(sK3(k1_wellord2(X7)),X7) | v8_relat_2(k1_wellord2(X7)) | ~v1_relat_1(k1_wellord2(X7))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f84,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.54    inference(global_subsumption,[],[f17,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.54    inference(equality_resolution,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X7] : (v8_relat_2(k1_wellord2(X7)) | ~v1_relat_1(k1_wellord2(X7)) | r2_hidden(sK3(k1_wellord2(X7)),k3_relat_1(k1_wellord2(X7)))) )),
% 0.21/0.54    inference(resolution,[],[f53,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k4_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(resolution,[],[f20,f17])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | v8_relat_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK3(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0)) | r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f221])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    ( ! [X0] : (v8_relat_2(k1_wellord2(X0)) | ~r2_hidden(sK3(k1_wellord2(X0)),X0) | r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))),k1_wellord2(X0)) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(resolution,[],[f219,f74])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r1_tarski(sK1(k1_wellord2(X3)),X2) | ~r2_hidden(X2,X3) | r2_hidden(k4_tarski(sK1(k1_wellord2(X3)),X2),k1_wellord2(X3)) | v8_relat_2(k1_wellord2(X3))) )),
% 0.21/0.54    inference(resolution,[],[f48,f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(sK1(k1_wellord2(X3)),X3) | v8_relat_2(k1_wellord2(X3))) )),
% 0.21/0.54    inference(global_subsumption,[],[f17,f62])).
% 0.21/0.54  % (6449)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X3] : (r2_hidden(sK1(k1_wellord2(X3)),X3) | v8_relat_2(k1_wellord2(X3)) | ~v1_relat_1(k1_wellord2(X3))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f59,f46])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X3] : (v8_relat_2(k1_wellord2(X3)) | ~v1_relat_1(k1_wellord2(X3)) | r2_hidden(sK1(k1_wellord2(X3)),k3_relat_1(k1_wellord2(X3)))) )),
% 0.21/0.54    inference(resolution,[],[f52,f32])).
% 0.21/0.54  % (6459)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(k4_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))),k1_wellord2(X0)) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(resolution,[],[f19,f17])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | v8_relat_2(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 0.21/0.54    inference(global_subsumption,[],[f17,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f216])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0)) | r1_tarski(sK1(k1_wellord2(X0)),sK3(k1_wellord2(X0)))) )),
% 0.21/0.54    inference(resolution,[],[f197,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK6(sK1(k1_wellord2(X0)),X1),sK3(k1_wellord2(X0))) | r1_tarski(sK1(k1_wellord2(X0)),X1) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f195])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(sK1(k1_wellord2(X0)),X1) | r2_hidden(sK6(sK1(k1_wellord2(X0)),X1),sK3(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0)) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(resolution,[],[f125,f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0)) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(resolution,[],[f111,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(sK2(k1_wellord2(X2)),X2) | v8_relat_2(k1_wellord2(X2))) )),
% 0.21/0.54    inference(global_subsumption,[],[f17,f60])).
% 0.21/0.54  % (6440)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(sK2(k1_wellord2(X2)),X2) | v8_relat_2(k1_wellord2(X2)) | ~v1_relat_1(k1_wellord2(X2))) )),
% 0.21/0.54    inference(forward_demodulation,[],[f58,f46])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X2] : (v8_relat_2(k1_wellord2(X2)) | ~v1_relat_1(k1_wellord2(X2)) | r2_hidden(sK2(k1_wellord2(X2)),k3_relat_1(k1_wellord2(X2)))) )),
% 0.21/0.54    inference(resolution,[],[f52,f33])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK2(k1_wellord2(X0)),X0) | r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f110])).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X0] : (v8_relat_2(k1_wellord2(X0)) | r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | ~r2_hidden(sK2(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(resolution,[],[f80,f87])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK3(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0)) | r1_tarski(sK2(k1_wellord2(X0)),sK3(k1_wellord2(X0))) | ~r2_hidden(sK2(k1_wellord2(X0)),X0)) )),
% 0.21/0.54    inference(resolution,[],[f53,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(global_subsumption,[],[f17,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X6,X4,X5] : (~r1_tarski(sK2(k1_wellord2(X4)),X6) | r1_tarski(sK1(k1_wellord2(X4)),X5) | r2_hidden(sK6(sK1(k1_wellord2(X4)),X5),X6) | v8_relat_2(k1_wellord2(X4))) )),
% 0.21/0.54    inference(resolution,[],[f70,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK6(sK1(k1_wellord2(X0)),X1),sK2(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0)) | r1_tarski(sK1(k1_wellord2(X0)),X1)) )),
% 0.21/0.54    inference(resolution,[],[f69,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK6(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f29,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(global_subsumption,[],[f61,f63,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(sK2(k1_wellord2(X0)),X0) | r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))) | ~r2_hidden(sK1(k1_wellord2(X0)),X0) | v8_relat_2(k1_wellord2(X0))) )),
% 0.21/0.54    inference(resolution,[],[f47,f52])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ~spl7_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f16,f42])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ~v8_relat_2(k1_wellord2(sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0] : ~v8_relat_2(k1_wellord2(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,negated_conjecture,(
% 0.21/0.54    ~! [X0] : v8_relat_2(k1_wellord2(X0))),
% 0.21/0.54    inference(negated_conjecture,[],[f6])).
% 0.21/0.54  fof(f6,conjecture,(
% 0.21/0.54    ! [X0] : v8_relat_2(k1_wellord2(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_wellord2)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (6455)------------------------------
% 0.21/0.54  % (6455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6455)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (6455)Memory used [KB]: 11001
% 0.21/0.54  % (6455)Time elapsed: 0.125 s
% 0.21/0.54  % (6455)------------------------------
% 0.21/0.54  % (6455)------------------------------
% 0.21/0.54  % (6464)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (6438)Success in time 0.178 s
%------------------------------------------------------------------------------
