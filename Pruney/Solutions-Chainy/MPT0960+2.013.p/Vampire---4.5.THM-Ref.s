%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:08 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 145 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   18
%              Number of atoms          :  180 ( 390 expanded)
%              Number of equality atoms :   26 (  56 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f297,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f294])).

fof(f294,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl10_1 ),
    inference(resolution,[],[f275,f60])).

fof(f60,plain,
    ( ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl10_1
  <=> r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f275,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(backward_demodulation,[],[f236,f268])).

fof(f268,plain,(
    ! [X7] : k2_relat_1(k1_wellord2(X7)) = X7 ),
    inference(global_subsumption,[],[f262])).

fof(f262,plain,(
    ! [X0] : k2_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f261,f124])).

fof(f124,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(k1_wellord2(X2)))
      | k2_relat_1(k1_wellord2(X2)) = X2 ) ),
    inference(resolution,[],[f122,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f122,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k1_wellord2(X0)),X0)
      | r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) ) ),
    inference(resolution,[],[f105,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k2_relat_1(k1_wellord2(X0)),X1),X0)
      | r1_tarski(k2_relat_1(k1_wellord2(X0)),X1) ) ),
    inference(forward_demodulation,[],[f104,f62])).

fof(f62,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f19,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | k3_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k1_wellord2(X0)),X1)
      | r2_hidden(sK3(k2_relat_1(k1_wellord2(X0)),X1),k3_relat_1(k1_wellord2(X0))) ) ),
    inference(resolution,[],[f86,f19])).

fof(f86,plain,(
    ! [X6,X7] :
      ( ~ v1_relat_1(X6)
      | r1_tarski(k2_relat_1(X6),X7)
      | r2_hidden(sK3(k2_relat_1(X6),X7),k3_relat_1(X6)) ) ),
    inference(resolution,[],[f71,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,sK3(k2_relat_1(X0),X1)),sK3(k2_relat_1(X0),X1)),X0)
      | r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(resolution,[],[f53,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f261,plain,(
    ! [X2] : r1_tarski(X2,k2_relat_1(k1_wellord2(X2))) ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,(
    ! [X2] :
      ( r1_tarski(X2,k2_relat_1(k1_wellord2(X2)))
      | r1_tarski(X2,k2_relat_1(k1_wellord2(X2))) ) ),
    inference(resolution,[],[f212,f33])).

fof(f212,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK3(X14,X15),k2_relat_1(k1_wellord2(X14)))
      | r1_tarski(X14,X15) ) ),
    inference(resolution,[],[f205,f54])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f205,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),k1_wellord2(X0))
      | r1_tarski(X0,X1) ) ),
    inference(global_subsumption,[],[f32,f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),k1_wellord2(X0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK3(X1,X2),X0)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(sK3(X1,X2),X0),k1_wellord2(X1))
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f64,f32])).

fof(f64,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    inference(global_subsumption,[],[f19,f50])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f236,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0)))) ),
    inference(backward_demodulation,[],[f67,f230])).

fof(f230,plain,(
    ! [X5] : k1_relat_1(k1_wellord2(X5)) = X5 ),
    inference(global_subsumption,[],[f225])).

fof(f225,plain,(
    ! [X0] : k1_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f220,f188])).

fof(f188,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_relat_1(k1_wellord2(X2)))
      | k1_relat_1(k1_wellord2(X2)) = X2 ) ),
    inference(resolution,[],[f186,f30])).

fof(f186,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_wellord2(X0)),X0) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_wellord2(X0)),X0)
      | r1_tarski(k1_relat_1(k1_wellord2(X0)),X0) ) ),
    inference(resolution,[],[f178,f33])).

fof(f178,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k1_relat_1(k1_wellord2(X0)),X1),X0)
      | r1_tarski(k1_relat_1(k1_wellord2(X0)),X1) ) ),
    inference(forward_demodulation,[],[f177,f62])).

fof(f177,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k1_wellord2(X0)),X1)
      | r2_hidden(sK3(k1_relat_1(k1_wellord2(X0)),X1),k3_relat_1(k1_wellord2(X0))) ) ),
    inference(resolution,[],[f171,f19])).

fof(f171,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | r1_tarski(k1_relat_1(X8),X9)
      | r2_hidden(sK3(k1_relat_1(X8),X9),k3_relat_1(X8)) ) ),
    inference(resolution,[],[f72,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(k1_relat_1(X0),X1),sK8(X0,sK3(k1_relat_1(X0),X1))),X0)
      | r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(resolution,[],[f55,f32])).

fof(f55,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f220,plain,(
    ! [X2] : r1_tarski(X2,k1_relat_1(k1_wellord2(X2))) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X2] :
      ( r1_tarski(X2,k1_relat_1(k1_wellord2(X2)))
      | r1_tarski(X2,k1_relat_1(k1_wellord2(X2))) ) ),
    inference(resolution,[],[f211,f33])).

fof(f211,plain,(
    ! [X12,X13] :
      ( r2_hidden(sK3(X12,X13),k1_relat_1(k1_wellord2(X12)))
      | r1_tarski(X12,X13) ) ),
    inference(resolution,[],[f205,f56])).

fof(f56,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) ),
    inference(resolution,[],[f20,f19])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f61,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f18,f58])).

fof(f18,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:50:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (419)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (412)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (408)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (419)Refutation not found, incomplete strategy% (419)------------------------------
% 0.21/0.51  % (419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (419)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (419)Memory used [KB]: 10746
% 0.21/0.51  % (419)Time elapsed: 0.027 s
% 0.21/0.51  % (419)------------------------------
% 0.21/0.51  % (419)------------------------------
% 0.21/0.51  % (399)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (400)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (422)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (417)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (417)Refutation not found, incomplete strategy% (417)------------------------------
% 0.21/0.52  % (417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (417)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (417)Memory used [KB]: 10746
% 0.21/0.52  % (417)Time elapsed: 0.115 s
% 0.21/0.52  % (417)------------------------------
% 0.21/0.52  % (417)------------------------------
% 0.21/0.52  % (405)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.28/0.53  % (424)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.53  % (407)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.54  % (396)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.54  % (397)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.54  % (397)Refutation not found, incomplete strategy% (397)------------------------------
% 1.28/0.54  % (397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (397)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (397)Memory used [KB]: 10746
% 1.28/0.54  % (397)Time elapsed: 0.133 s
% 1.28/0.54  % (397)------------------------------
% 1.28/0.54  % (397)------------------------------
% 1.28/0.54  % (401)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.43/0.55  % (423)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.43/0.55  % (421)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.55  % (425)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.43/0.55  % (416)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (414)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.55  % (406)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.56  % (404)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.56  % (404)Refutation not found, incomplete strategy% (404)------------------------------
% 1.43/0.56  % (404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (404)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (404)Memory used [KB]: 10618
% 1.43/0.56  % (404)Time elapsed: 0.148 s
% 1.43/0.56  % (404)------------------------------
% 1.43/0.56  % (404)------------------------------
% 1.43/0.57  % (409)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.57  % (395)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.43/0.58  % (410)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.58  % (418)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.58  % (418)Refutation not found, incomplete strategy% (418)------------------------------
% 1.43/0.58  % (418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.58  % (418)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.58  
% 1.43/0.58  % (418)Memory used [KB]: 1663
% 1.43/0.58  % (418)Time elapsed: 0.178 s
% 1.43/0.58  % (418)------------------------------
% 1.43/0.58  % (418)------------------------------
% 1.43/0.58  % (413)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.58  % (402)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.43/0.59  % (415)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.59  % (427)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.59  % (403)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.60  % (441)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.43/0.60  % (420)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.61  % (413)Refutation found. Thanks to Tanya!
% 1.43/0.61  % SZS status Theorem for theBenchmark
% 1.43/0.61  % SZS output start Proof for theBenchmark
% 1.43/0.61  fof(f297,plain,(
% 1.43/0.61    $false),
% 1.43/0.61    inference(avatar_sat_refutation,[],[f61,f294])).
% 1.43/0.61  fof(f294,plain,(
% 1.43/0.61    spl10_1),
% 1.43/0.61    inference(avatar_contradiction_clause,[],[f289])).
% 1.43/0.61  fof(f289,plain,(
% 1.43/0.61    $false | spl10_1),
% 1.43/0.61    inference(resolution,[],[f275,f60])).
% 1.43/0.61  fof(f60,plain,(
% 1.43/0.61    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) | spl10_1),
% 1.43/0.61    inference(avatar_component_clause,[],[f58])).
% 1.43/0.61  fof(f58,plain,(
% 1.43/0.61    spl10_1 <=> r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 1.43/0.61    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.43/0.61  fof(f275,plain,(
% 1.43/0.61    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 1.43/0.61    inference(backward_demodulation,[],[f236,f268])).
% 1.43/0.61  fof(f268,plain,(
% 1.43/0.61    ( ! [X7] : (k2_relat_1(k1_wellord2(X7)) = X7) )),
% 1.43/0.61    inference(global_subsumption,[],[f262])).
% 1.43/0.61  fof(f262,plain,(
% 1.43/0.61    ( ! [X0] : (k2_relat_1(k1_wellord2(X0)) = X0) )),
% 1.43/0.61    inference(resolution,[],[f261,f124])).
% 1.43/0.61  fof(f124,plain,(
% 1.43/0.61    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(k1_wellord2(X2))) | k2_relat_1(k1_wellord2(X2)) = X2) )),
% 1.43/0.61    inference(resolution,[],[f122,f30])).
% 1.43/0.61  fof(f30,plain,(
% 1.43/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.43/0.61    inference(cnf_transformation,[],[f2])).
% 1.43/0.61  fof(f2,axiom,(
% 1.43/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.61  fof(f122,plain,(
% 1.43/0.61    ( ! [X0] : (r1_tarski(k2_relat_1(k1_wellord2(X0)),X0)) )),
% 1.43/0.61    inference(duplicate_literal_removal,[],[f117])).
% 1.43/0.61  fof(f117,plain,(
% 1.43/0.61    ( ! [X0] : (r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) | r1_tarski(k2_relat_1(k1_wellord2(X0)),X0)) )),
% 1.43/0.61    inference(resolution,[],[f105,f33])).
% 1.43/0.61  fof(f33,plain,(
% 1.43/0.61    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.43/0.61    inference(cnf_transformation,[],[f15])).
% 1.43/0.61  fof(f15,plain,(
% 1.43/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.43/0.61    inference(ennf_transformation,[],[f1])).
% 1.43/0.61  fof(f1,axiom,(
% 1.43/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.43/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.43/0.61  fof(f105,plain,(
% 1.43/0.61    ( ! [X0,X1] : (r2_hidden(sK3(k2_relat_1(k1_wellord2(X0)),X1),X0) | r1_tarski(k2_relat_1(k1_wellord2(X0)),X1)) )),
% 1.43/0.61    inference(forward_demodulation,[],[f104,f62])).
% 1.43/0.61  fof(f62,plain,(
% 1.43/0.61    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 1.43/0.61    inference(global_subsumption,[],[f19,f44])).
% 1.43/0.61  fof(f44,plain,(
% 1.43/0.61    ( ! [X0] : (~v1_relat_1(k1_wellord2(X0)) | k3_relat_1(k1_wellord2(X0)) = X0) )),
% 1.43/0.61    inference(equality_resolution,[],[f27])).
% 1.43/0.61  fof(f27,plain,(
% 1.43/0.61    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 1.43/0.61    inference(cnf_transformation,[],[f14])).
% 1.43/0.61  fof(f14,plain,(
% 1.43/0.61    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.43/0.61    inference(flattening,[],[f13])).
% 1.43/0.61  fof(f13,plain,(
% 1.43/0.61    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.43/0.61    inference(ennf_transformation,[],[f7])).
% 1.43/0.61  fof(f7,axiom,(
% 1.43/0.61    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 1.43/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 1.43/0.61  fof(f19,plain,(
% 1.43/0.61    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 1.43/0.61    inference(cnf_transformation,[],[f8])).
% 1.43/0.61  fof(f8,axiom,(
% 1.43/0.61    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 1.43/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 1.43/0.61  fof(f104,plain,(
% 1.43/0.61    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k1_wellord2(X0)),X1) | r2_hidden(sK3(k2_relat_1(k1_wellord2(X0)),X1),k3_relat_1(k1_wellord2(X0)))) )),
% 1.43/0.61    inference(resolution,[],[f86,f19])).
% 1.43/0.61  fof(f86,plain,(
% 1.43/0.61    ( ! [X6,X7] : (~v1_relat_1(X6) | r1_tarski(k2_relat_1(X6),X7) | r2_hidden(sK3(k2_relat_1(X6),X7),k3_relat_1(X6))) )),
% 1.43/0.61    inference(resolution,[],[f71,f43])).
% 1.43/0.61  fof(f43,plain,(
% 1.43/0.61    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 1.43/0.61    inference(cnf_transformation,[],[f17])).
% 1.43/0.61  fof(f17,plain,(
% 1.43/0.61    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.43/0.61    inference(flattening,[],[f16])).
% 1.43/0.61  fof(f16,plain,(
% 1.43/0.61    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.43/0.61    inference(ennf_transformation,[],[f6])).
% 1.43/0.61  fof(f6,axiom,(
% 1.43/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 1.43/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 1.43/0.61  fof(f71,plain,(
% 1.43/0.61    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,sK3(k2_relat_1(X0),X1)),sK3(k2_relat_1(X0),X1)),X0) | r1_tarski(k2_relat_1(X0),X1)) )),
% 1.43/0.61    inference(resolution,[],[f53,f32])).
% 1.43/0.61  fof(f32,plain,(
% 1.43/0.61    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.43/0.61    inference(cnf_transformation,[],[f15])).
% 1.43/0.61  fof(f53,plain,(
% 1.43/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)) )),
% 1.43/0.61    inference(equality_resolution,[],[f35])).
% 1.43/0.61  fof(f35,plain,(
% 1.43/0.61    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.43/0.61    inference(cnf_transformation,[],[f4])).
% 1.43/0.61  fof(f4,axiom,(
% 1.43/0.61    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.43/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.43/0.61  fof(f261,plain,(
% 1.43/0.61    ( ! [X2] : (r1_tarski(X2,k2_relat_1(k1_wellord2(X2)))) )),
% 1.43/0.61    inference(duplicate_literal_removal,[],[f258])).
% 1.43/0.61  fof(f258,plain,(
% 1.43/0.61    ( ! [X2] : (r1_tarski(X2,k2_relat_1(k1_wellord2(X2))) | r1_tarski(X2,k2_relat_1(k1_wellord2(X2)))) )),
% 1.43/0.61    inference(resolution,[],[f212,f33])).
% 1.43/0.61  fof(f212,plain,(
% 1.43/0.61    ( ! [X14,X15] : (r2_hidden(sK3(X14,X15),k2_relat_1(k1_wellord2(X14))) | r1_tarski(X14,X15)) )),
% 1.43/0.61    inference(resolution,[],[f205,f54])).
% 1.43/0.61  fof(f54,plain,(
% 1.43/0.61    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 1.43/0.61    inference(equality_resolution,[],[f34])).
% 1.43/0.61  fof(f34,plain,(
% 1.43/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.43/0.61    inference(cnf_transformation,[],[f4])).
% 1.43/0.61  fof(f205,plain,(
% 1.43/0.61    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),k1_wellord2(X0)) | r1_tarski(X0,X1)) )),
% 1.43/0.61    inference(global_subsumption,[],[f32,f204])).
% 1.43/0.61  fof(f204,plain,(
% 1.43/0.61    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X0) | r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),k1_wellord2(X0)) | r1_tarski(X0,X1)) )),
% 1.43/0.61    inference(resolution,[],[f79,f51])).
% 1.43/0.61  fof(f51,plain,(
% 1.43/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.43/0.61    inference(equality_resolution,[],[f29])).
% 1.43/0.61  fof(f29,plain,(
% 1.43/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.43/0.61    inference(cnf_transformation,[],[f2])).
% 1.43/0.61  fof(f79,plain,(
% 1.43/0.61    ( ! [X2,X0,X1] : (~r1_tarski(sK3(X1,X2),X0) | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(sK3(X1,X2),X0),k1_wellord2(X1)) | r1_tarski(X1,X2)) )),
% 1.43/0.61    inference(resolution,[],[f64,f32])).
% 1.43/0.61  fof(f64,plain,(
% 1.43/0.61    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 1.43/0.61    inference(global_subsumption,[],[f19,f50])).
% 1.43/0.61  fof(f50,plain,(
% 1.43/0.61    ( ! [X2,X0,X3] : (~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),k1_wellord2(X0))) )),
% 1.43/0.61    inference(equality_resolution,[],[f21])).
% 1.43/0.61  fof(f21,plain,(
% 1.43/0.61    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 1.43/0.61    inference(cnf_transformation,[],[f14])).
% 1.43/0.61  fof(f236,plain,(
% 1.43/0.61    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,k2_relat_1(k1_wellord2(X0))))) )),
% 1.43/0.61    inference(backward_demodulation,[],[f67,f230])).
% 1.43/0.61  fof(f230,plain,(
% 1.43/0.61    ( ! [X5] : (k1_relat_1(k1_wellord2(X5)) = X5) )),
% 1.43/0.61    inference(global_subsumption,[],[f225])).
% 1.43/0.61  fof(f225,plain,(
% 1.43/0.61    ( ! [X0] : (k1_relat_1(k1_wellord2(X0)) = X0) )),
% 1.43/0.61    inference(resolution,[],[f220,f188])).
% 1.43/0.61  fof(f188,plain,(
% 1.43/0.61    ( ! [X2] : (~r1_tarski(X2,k1_relat_1(k1_wellord2(X2))) | k1_relat_1(k1_wellord2(X2)) = X2) )),
% 1.43/0.61    inference(resolution,[],[f186,f30])).
% 1.43/0.61  fof(f186,plain,(
% 1.43/0.61    ( ! [X0] : (r1_tarski(k1_relat_1(k1_wellord2(X0)),X0)) )),
% 1.43/0.61    inference(duplicate_literal_removal,[],[f181])).
% 1.43/0.61  fof(f181,plain,(
% 1.43/0.61    ( ! [X0] : (r1_tarski(k1_relat_1(k1_wellord2(X0)),X0) | r1_tarski(k1_relat_1(k1_wellord2(X0)),X0)) )),
% 1.43/0.61    inference(resolution,[],[f178,f33])).
% 1.43/0.61  fof(f178,plain,(
% 1.43/0.61    ( ! [X0,X1] : (r2_hidden(sK3(k1_relat_1(k1_wellord2(X0)),X1),X0) | r1_tarski(k1_relat_1(k1_wellord2(X0)),X1)) )),
% 1.43/0.61    inference(forward_demodulation,[],[f177,f62])).
% 1.43/0.61  fof(f177,plain,(
% 1.43/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k1_wellord2(X0)),X1) | r2_hidden(sK3(k1_relat_1(k1_wellord2(X0)),X1),k3_relat_1(k1_wellord2(X0)))) )),
% 1.43/0.61    inference(resolution,[],[f171,f19])).
% 1.43/0.61  fof(f171,plain,(
% 1.43/0.61    ( ! [X8,X9] : (~v1_relat_1(X8) | r1_tarski(k1_relat_1(X8),X9) | r2_hidden(sK3(k1_relat_1(X8),X9),k3_relat_1(X8))) )),
% 1.43/0.61    inference(resolution,[],[f72,f42])).
% 1.43/0.61  fof(f42,plain,(
% 1.43/0.61    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 1.43/0.61    inference(cnf_transformation,[],[f17])).
% 1.43/0.61  fof(f72,plain,(
% 1.43/0.61    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(k1_relat_1(X0),X1),sK8(X0,sK3(k1_relat_1(X0),X1))),X0) | r1_tarski(k1_relat_1(X0),X1)) )),
% 1.43/0.61    inference(resolution,[],[f55,f32])).
% 1.43/0.61  fof(f55,plain,(
% 1.43/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0)) )),
% 1.43/0.61    inference(equality_resolution,[],[f39])).
% 1.43/0.61  fof(f39,plain,(
% 1.43/0.61    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK8(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.43/0.61    inference(cnf_transformation,[],[f3])).
% 1.43/0.61  fof(f3,axiom,(
% 1.43/0.61    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.43/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.43/0.61  fof(f220,plain,(
% 1.43/0.61    ( ! [X2] : (r1_tarski(X2,k1_relat_1(k1_wellord2(X2)))) )),
% 1.43/0.61    inference(duplicate_literal_removal,[],[f217])).
% 1.43/0.61  fof(f217,plain,(
% 1.43/0.61    ( ! [X2] : (r1_tarski(X2,k1_relat_1(k1_wellord2(X2))) | r1_tarski(X2,k1_relat_1(k1_wellord2(X2)))) )),
% 1.43/0.61    inference(resolution,[],[f211,f33])).
% 1.43/0.61  fof(f211,plain,(
% 1.43/0.61    ( ! [X12,X13] : (r2_hidden(sK3(X12,X13),k1_relat_1(k1_wellord2(X12))) | r1_tarski(X12,X13)) )),
% 1.43/0.61    inference(resolution,[],[f205,f56])).
% 1.43/0.61  fof(f56,plain,(
% 1.43/0.61    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 1.43/0.61    inference(equality_resolution,[],[f38])).
% 1.43/0.61  fof(f38,plain,(
% 1.43/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.43/0.61    inference(cnf_transformation,[],[f3])).
% 1.43/0.61  fof(f67,plain,(
% 1.43/0.61    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))))) )),
% 1.43/0.61    inference(resolution,[],[f20,f19])).
% 1.43/0.61  fof(f20,plain,(
% 1.43/0.61    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 1.43/0.61    inference(cnf_transformation,[],[f12])).
% 1.43/0.61  fof(f12,plain,(
% 1.43/0.61    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.43/0.61    inference(ennf_transformation,[],[f5])).
% 1.43/0.61  fof(f5,axiom,(
% 1.43/0.61    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.43/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 1.43/0.61  fof(f61,plain,(
% 1.43/0.61    ~spl10_1),
% 1.43/0.61    inference(avatar_split_clause,[],[f18,f58])).
% 1.43/0.61  fof(f18,plain,(
% 1.43/0.61    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 1.43/0.61    inference(cnf_transformation,[],[f11])).
% 1.43/0.61  fof(f11,plain,(
% 1.43/0.61    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 1.43/0.61    inference(ennf_transformation,[],[f10])).
% 1.43/0.61  fof(f10,negated_conjecture,(
% 1.43/0.61    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 1.43/0.61    inference(negated_conjecture,[],[f9])).
% 1.43/0.61  fof(f9,conjecture,(
% 1.43/0.61    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 1.43/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
% 1.43/0.61  % SZS output end Proof for theBenchmark
% 1.43/0.61  % (413)------------------------------
% 1.43/0.61  % (413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.61  % (413)Termination reason: Refutation
% 1.43/0.61  
% 1.43/0.61  % (413)Memory used [KB]: 11129
% 1.43/0.61  % (413)Time elapsed: 0.213 s
% 1.43/0.61  % (413)------------------------------
% 1.43/0.61  % (413)------------------------------
% 2.01/0.63  % (442)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.01/0.63  % (393)Success in time 0.266 s
%------------------------------------------------------------------------------
