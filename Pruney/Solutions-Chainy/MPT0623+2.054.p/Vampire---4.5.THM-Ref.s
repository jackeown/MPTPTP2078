%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 600 expanded)
%              Number of leaves         :    7 ( 152 expanded)
%              Depth                    :   16
%              Number of atoms          :  133 (2191 expanded)
%              Number of equality atoms :   42 ( 789 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f110,f213])).

fof(f213,plain,(
    ~ spl14_1 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl14_1 ),
    inference(unit_resulting_resolution,[],[f132,f121,f156,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f156,plain,
    ( ! [X0] : r2_hidden(sK7(sK9(k1_xboole_0,X0),X0),k1_xboole_0)
    | ~ spl14_1 ),
    inference(backward_demodulation,[],[f85,f51])).

fof(f51,plain,
    ( k1_xboole_0 = sK1
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl14_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f85,plain,(
    ! [X0] : r2_hidden(sK7(sK9(sK1,X0),X0),sK1) ),
    inference(backward_demodulation,[],[f76,f79])).

fof(f79,plain,(
    ! [X0] : sK2(k2_relat_1(sK9(sK1,X0)),sK0) = X0 ),
    inference(backward_demodulation,[],[f71,f77])).

fof(f77,plain,(
    ! [X0,X1] : k1_funct_1(sK9(sK1,X0),sK7(sK9(sK1,X1),sK2(k2_relat_1(sK9(sK1,X1)),sK0))) = X0 ),
    inference(unit_resulting_resolution,[],[f76,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK9(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f71,plain,(
    ! [X0] : sK2(k2_relat_1(sK9(sK1,X0)),sK0) = k1_funct_1(sK9(sK1,X0),sK7(sK9(sK1,X0),sK2(k2_relat_1(sK9(sK1,X0)),sK0))) ),
    inference(unit_resulting_resolution,[],[f33,f32,f67,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK7(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK7(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f67,plain,(
    ! [X0] : r2_hidden(sK2(k2_relat_1(sK9(sK1,X0)),sK0),k2_relat_1(sK9(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f65,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK9(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f32,f33,f34,f16])).

fof(f16,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f34,plain,(
    ! [X0,X1] : k1_relat_1(sK9(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] : v1_relat_1(sK9(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] : v1_funct_1(sK9(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0] : r2_hidden(sK7(sK9(sK1,X0),sK2(k2_relat_1(sK9(sK1,X0)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f70,f34])).

fof(f70,plain,(
    ! [X0] : r2_hidden(sK7(sK9(sK1,X0),sK2(k2_relat_1(sK9(sK1,X0)),sK0)),k1_relat_1(sK9(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f33,f32,f67,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK7(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK7(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f81,f97])).

fof(f97,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f81,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK13(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f81,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f68,f79])).

fof(f68,plain,(
    ! [X0] : ~ r2_hidden(sK2(k2_relat_1(sK9(sK1,X0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f65,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f132,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f94,f97])).

fof(f94,plain,(
    ! [X0] : r1_tarski(sK0,X0) ),
    inference(unit_resulting_resolution,[],[f81,f19])).

fof(f110,plain,(
    spl14_2 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl14_2 ),
    inference(unit_resulting_resolution,[],[f55,f81,f39])).

fof(f55,plain,
    ( k1_xboole_0 != sK0
    | spl14_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl14_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f56,plain,
    ( spl14_1
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f17,f53,f49])).

fof(f17,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (7039)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (7055)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (7032)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (7047)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (7041)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (7049)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (7031)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (7036)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (7049)Refutation not found, incomplete strategy% (7049)------------------------------
% 0.20/0.52  % (7049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7033)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (7049)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7049)Memory used [KB]: 10746
% 0.20/0.52  % (7049)Time elapsed: 0.066 s
% 0.20/0.52  % (7049)------------------------------
% 0.20/0.52  % (7049)------------------------------
% 0.20/0.52  % (7047)Refutation not found, incomplete strategy% (7047)------------------------------
% 0.20/0.52  % (7047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7048)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (7047)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7047)Memory used [KB]: 10746
% 0.20/0.52  % (7047)Time elapsed: 0.118 s
% 0.20/0.52  % (7047)------------------------------
% 0.20/0.52  % (7047)------------------------------
% 0.20/0.52  % (7048)Refutation not found, incomplete strategy% (7048)------------------------------
% 0.20/0.52  % (7048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7048)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7048)Memory used [KB]: 1663
% 0.20/0.52  % (7048)Time elapsed: 0.124 s
% 0.20/0.52  % (7048)------------------------------
% 0.20/0.52  % (7048)------------------------------
% 0.20/0.53  % (7028)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (7040)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (7027)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (7027)Refutation not found, incomplete strategy% (7027)------------------------------
% 0.20/0.53  % (7027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7027)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7027)Memory used [KB]: 1663
% 0.20/0.53  % (7027)Time elapsed: 0.124 s
% 0.20/0.53  % (7027)------------------------------
% 0.20/0.53  % (7027)------------------------------
% 0.20/0.53  % (7054)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (7029)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (7030)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (7029)Refutation not found, incomplete strategy% (7029)------------------------------
% 0.20/0.53  % (7029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7029)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7029)Memory used [KB]: 10746
% 0.20/0.53  % (7029)Time elapsed: 0.136 s
% 0.20/0.53  % (7029)------------------------------
% 0.20/0.53  % (7029)------------------------------
% 0.20/0.53  % (7042)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (7056)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (7036)Refutation not found, incomplete strategy% (7036)------------------------------
% 0.20/0.54  % (7036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7036)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (7036)Memory used [KB]: 10618
% 0.20/0.54  % (7036)Time elapsed: 0.135 s
% 0.20/0.54  % (7036)------------------------------
% 0.20/0.54  % (7036)------------------------------
% 0.20/0.54  % (7035)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (7037)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (7031)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f56,f110,f213])).
% 0.20/0.54  fof(f213,plain,(
% 0.20/0.54    ~spl14_1),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f208])).
% 0.20/0.54  fof(f208,plain,(
% 0.20/0.54    $false | ~spl14_1),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f132,f121,f156,f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK7(sK9(k1_xboole_0,X0),X0),k1_xboole_0)) ) | ~spl14_1),
% 0.20/0.54    inference(backward_demodulation,[],[f85,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | ~spl14_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    spl14_1 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK7(sK9(sK1,X0),X0),sK1)) )),
% 0.20/0.54    inference(backward_demodulation,[],[f76,f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X0] : (sK2(k2_relat_1(sK9(sK1,X0)),sK0) = X0) )),
% 0.20/0.54    inference(backward_demodulation,[],[f71,f77])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_funct_1(sK9(sK1,X0),sK7(sK9(sK1,X1),sK2(k2_relat_1(sK9(sK1,X1)),sK0))) = X0) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f76,f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (k1_funct_1(sK9(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X0] : (sK2(k2_relat_1(sK9(sK1,X0)),sK0) = k1_funct_1(sK9(sK1,X0),sK7(sK9(sK1,X0),sK2(k2_relat_1(sK9(sK1,X0)),sK0)))) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f33,f32,f67,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK7(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.54    inference(equality_resolution,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK7(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK2(k2_relat_1(sK9(sK1,X0)),sK0),k2_relat_1(sK9(sK1,X0)))) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f65,f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK9(sK1,X0)),sK0)) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f32,f33,f34,f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.20/0.54    inference(flattening,[],[f9])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.54    inference(negated_conjecture,[],[f7])).
% 0.20/0.54  fof(f7,conjecture,(
% 0.20/0.54    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k1_relat_1(sK9(X0,X1)) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(sK9(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_funct_1(sK9(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK7(sK9(sK1,X0),sK2(k2_relat_1(sK9(sK1,X0)),sK0)),sK1)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f70,f34])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK7(sK9(sK1,X0),sK2(k2_relat_1(sK9(sK1,X0)),sK0)),k1_relat_1(sK9(sK1,X0)))) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f33,f32,f67,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK7(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.54    inference(equality_resolution,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK7(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(backward_demodulation,[],[f81,f97])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    k1_xboole_0 = sK0),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f81,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK13(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.20/0.54    inference(backward_demodulation,[],[f68,f79])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(sK2(k2_relat_1(sK9(sK1,X0)),sK0),sK0)) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f65,f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f132,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f94,f97])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(sK0,X0)) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f81,f19])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    spl14_2),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f98])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    $false | spl14_2),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f55,f81,f39])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    k1_xboole_0 != sK0 | spl14_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    spl14_2 <=> k1_xboole_0 = sK0),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    spl14_1 | ~spl14_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f17,f53,f49])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (7031)------------------------------
% 0.20/0.54  % (7031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7031)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (7031)Memory used [KB]: 6268
% 0.20/0.54  % (7031)Time elapsed: 0.121 s
% 0.20/0.54  % (7031)------------------------------
% 0.20/0.54  % (7031)------------------------------
% 0.20/0.54  % (7035)Refutation not found, incomplete strategy% (7035)------------------------------
% 0.20/0.54  % (7035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (7035)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (7035)Memory used [KB]: 10618
% 0.20/0.54  % (7035)Time elapsed: 0.134 s
% 0.20/0.54  % (7035)------------------------------
% 0.20/0.54  % (7035)------------------------------
% 0.20/0.54  % (7022)Success in time 0.18 s
%------------------------------------------------------------------------------
