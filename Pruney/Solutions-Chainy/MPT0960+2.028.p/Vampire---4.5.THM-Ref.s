%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  92 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  152 ( 238 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f49,f63,f68,f76,f93,f112])).

fof(f112,plain,
    ( spl5_1
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl5_1
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f110,f41])).

fof(f41,plain,
    ( ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_1
  <=> r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f110,plain,
    ( r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f109,f15])).

fof(f15,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f109,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f104,f92])).

fof(f92,plain,
    ( r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_6
  <=> r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f104,plain,
    ( ~ r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))
    | ~ spl5_5 ),
    inference(resolution,[],[f82,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f82,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),X0),k2_zfmisc_1(sK0,X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f75,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f75,plain,
    ( r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl5_5
  <=> r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f93,plain,
    ( spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f79,f65,f90])).

fof(f65,plain,
    ( spl5_4
  <=> r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f79,plain,
    ( r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0)
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f78,f15])).

fof(f78,plain,
    ( r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_4 ),
    inference(superposition,[],[f67,f31])).

fof(f31,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f67,plain,
    ( r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f76,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f71,f60,f73])).

fof(f60,plain,
    ( spl5_3
  <=> r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f71,plain,
    ( r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f70,f15])).

fof(f70,plain,
    ( r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_3 ),
    inference(superposition,[],[f62,f31])).

fof(f62,plain,
    ( r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f68,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f57,f46,f65])).

fof(f46,plain,
    ( spl5_2
  <=> r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f57,plain,
    ( r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f52,f15])).

fof(f52,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_2 ),
    inference(resolution,[],[f48,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f48,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),k1_wellord2(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f63,plain,
    ( spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f56,f46,f60])).

fof(f56,plain,
    ( r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f51,f15])).

fof(f51,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_2 ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f49,plain,
    ( spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f44,f39,f46])).

fof(f44,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),k1_wellord2(sK0))
    | spl5_1 ),
    inference(subsumption_resolution,[],[f43,f15])).

fof(f43,plain,
    ( r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_1 ),
    inference(resolution,[],[f41,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f14,f39])).

fof(f14,plain,(
    ~ r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:22:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (20775)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (20774)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (20767)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (20763)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (20766)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (20763)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f42,f49,f63,f68,f76,f93,f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl5_1 | ~spl5_5 | ~spl5_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    $false | (spl5_1 | ~spl5_5 | ~spl5_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f110,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) | spl5_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl5_1 <=> r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) | (~spl5_5 | ~spl5_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ~v1_relat_1(k1_wellord2(sK0)) | r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) | (~spl5_5 | ~spl5_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f104,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0) | ~spl5_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl5_6 <=> r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ~r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f82,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) | ~v1_relat_1(X0) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),X0),k2_zfmisc_1(sK0,X1)) | ~r2_hidden(X0,X1)) ) | ~spl5_5),
% 0.21/0.49    inference(resolution,[],[f75,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0) | ~spl5_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl5_5 <=> r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl5_6 | ~spl5_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f79,f65,f90])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl5_4 <=> r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0) | ~spl5_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f78,f15])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_4),
% 0.21/0.49    inference(superposition,[],[f67,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0))) | ~spl5_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl5_5 | ~spl5_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f71,f60,f73])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    spl5_3 <=> r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0) | ~spl5_3),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f15])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK0) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_3),
% 0.21/0.49    inference(superposition,[],[f62,f31])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0))) | ~spl5_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f60])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl5_4 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f57,f46,f65])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl5_2 <=> r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),k1_wellord2(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0))) | ~spl5_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f52,f15])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ~v1_relat_1(k1_wellord2(sK0)) | r2_hidden(sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0))) | ~spl5_2),
% 0.21/0.49    inference(resolution,[],[f48,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),k1_wellord2(sK0)) | ~spl5_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f46])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl5_3 | ~spl5_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f46,f60])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0))) | ~spl5_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f51,f15])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ~v1_relat_1(k1_wellord2(sK0)) | r2_hidden(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),k3_relat_1(k1_wellord2(sK0))) | ~spl5_2),
% 0.21/0.49    inference(resolution,[],[f48,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k3_relat_1(X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl5_2 | spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f39,f46])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),k1_wellord2(sK0)) | spl5_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f43,f15])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK1(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0)),sK2(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK0)) | spl5_1),
% 0.21/0.49    inference(resolution,[],[f41,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ~spl5_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f14,f39])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ~r1_tarski(k1_wellord2(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (20763)------------------------------
% 0.21/0.49  % (20763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20763)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (20763)Memory used [KB]: 10618
% 0.21/0.49  % (20763)Time elapsed: 0.072 s
% 0.21/0.49  % (20763)------------------------------
% 0.21/0.49  % (20763)------------------------------
% 0.21/0.49  % (20759)Success in time 0.127 s
%------------------------------------------------------------------------------
