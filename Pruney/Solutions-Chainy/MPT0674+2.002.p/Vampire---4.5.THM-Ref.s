%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:25 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 233 expanded)
%              Number of leaves         :    6 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 774 expanded)
%              Number of equality atoms :   44 ( 229 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f844,plain,(
    $false ),
    inference(subsumption_resolution,[],[f843,f173])).

fof(f173,plain,(
    r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f20,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | k1_tarski(X0) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X0
      | k1_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X0
      | k1_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(superposition,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1)
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | sK2(X0,X1) != X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,plain,(
    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f79,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f72,f52])).

fof(f52,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0)) ),
    inference(unit_resulting_resolution,[],[f17,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f72,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,k1_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f18,f17,f59,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f59,plain,(
    sP4(k1_funct_1(sK1,sK0),k1_tarski(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f44,f19,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | sP4(k1_funct_1(X0,X4),X1,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f19,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f843,plain,(
    ~ r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f842,f52])).

fof(f842,plain,(
    ~ r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k9_relat_1(sK1,k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f834,f270])).

fof(f270,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),sK1) ),
    inference(unit_resulting_resolution,[],[f222,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | k1_funct_1(sK1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f63,f17])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),sK1) ) ),
    inference(resolution,[],[f22,f18])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f222,plain,(
    k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f20,f173,f27])).

fof(f834,plain,
    ( r2_hidden(k4_tarski(sK0,sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),sK1)
    | ~ r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k9_relat_1(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f90,f313])).

fof(f313,plain,(
    sK0 = sK6(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k1_tarski(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f173,f231])).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k11_relat_1(sK1,X1))
      | sK6(X0,k1_tarski(X1),sK1) = X1 ) ),
    inference(resolution,[],[f129,f42])).

fof(f42,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1,k1_tarski(X0),sK1),k1_tarski(X0))
      | ~ r2_hidden(X1,k11_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f53,f52])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK1,X1))
      | r2_hidden(sK6(X0,X1,sK1),X1) ) ),
    inference(resolution,[],[f39,f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,sK1),X0),sK1)
      | ~ r2_hidden(X0,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f38,f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (30155)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (30164)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (30156)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (30158)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (30184)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (30164)Refutation not found, incomplete strategy% (30164)------------------------------
% 0.20/0.51  % (30164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30164)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (30164)Memory used [KB]: 10746
% 0.20/0.51  % (30164)Time elapsed: 0.102 s
% 0.20/0.51  % (30164)------------------------------
% 0.20/0.51  % (30164)------------------------------
% 0.20/0.51  % (30173)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.51  % (30157)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (30160)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (30153)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (30175)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (30159)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (30165)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (30172)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (30163)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (30154)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (30167)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (30177)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (30166)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (30181)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (30176)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (30171)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (30179)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (30174)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (30178)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (30169)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (30183)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (30182)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (30170)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (30168)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (30183)Refutation not found, incomplete strategy% (30183)------------------------------
% 0.20/0.54  % (30183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (30183)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (30183)Memory used [KB]: 10746
% 0.20/0.54  % (30183)Time elapsed: 0.136 s
% 0.20/0.54  % (30183)------------------------------
% 0.20/0.54  % (30183)------------------------------
% 0.20/0.55  % (30162)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.56  % (30170)Refutation not found, incomplete strategy% (30170)------------------------------
% 0.20/0.56  % (30170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (30170)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (30170)Memory used [KB]: 10618
% 0.20/0.56  % (30170)Time elapsed: 0.161 s
% 0.20/0.56  % (30170)------------------------------
% 0.20/0.56  % (30170)------------------------------
% 1.55/0.56  % (30173)Refutation found. Thanks to Tanya!
% 1.55/0.56  % SZS status Theorem for theBenchmark
% 1.55/0.56  % SZS output start Proof for theBenchmark
% 1.55/0.56  fof(f844,plain,(
% 1.55/0.56    $false),
% 1.55/0.56    inference(subsumption_resolution,[],[f843,f173])).
% 1.55/0.56  fof(f173,plain,(
% 1.55/0.56    r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f79,f20,f86])).
% 1.55/0.56  fof(f86,plain,(
% 1.55/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | k1_tarski(X0) = X1 | ~r2_hidden(X0,X1)) )),
% 1.55/0.56    inference(trivial_inequality_removal,[],[f85])).
% 1.55/0.56  fof(f85,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | X0 != X0 | k1_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X1)) )),
% 1.55/0.56    inference(duplicate_literal_removal,[],[f84])).
% 1.55/0.56  fof(f84,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | X0 != X0 | k1_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.55/0.56    inference(superposition,[],[f27,f26])).
% 1.55/0.56  fof(f26,plain,(
% 1.55/0.56    ( ! [X0,X1] : (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1) | k1_tarski(X0) = X1) )),
% 1.55/0.56    inference(cnf_transformation,[],[f1])).
% 1.55/0.56  fof(f1,axiom,(
% 1.55/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.55/0.56  fof(f27,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) != X0 | k1_tarski(X0) = X1) )),
% 1.55/0.56    inference(cnf_transformation,[],[f1])).
% 1.55/0.56  fof(f20,plain,(
% 1.55/0.56    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.55/0.56    inference(cnf_transformation,[],[f10])).
% 1.55/0.56  fof(f10,plain,(
% 1.55/0.56    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.55/0.56    inference(flattening,[],[f9])).
% 1.55/0.56  fof(f9,plain,(
% 1.55/0.56    ? [X0,X1] : ((k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.55/0.56    inference(ennf_transformation,[],[f8])).
% 1.55/0.56  fof(f8,negated_conjecture,(
% 1.55/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.55/0.56    inference(negated_conjecture,[],[f7])).
% 1.55/0.56  fof(f7,conjecture,(
% 1.55/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 1.55/0.56  fof(f79,plain,(
% 1.55/0.56    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 1.55/0.56    inference(forward_demodulation,[],[f72,f52])).
% 1.55/0.56  fof(f52,plain,(
% 1.55/0.56    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_tarski(X0))) )),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f17,f36])).
% 1.55/0.56  fof(f36,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f15])).
% 1.55/0.56  fof(f15,plain,(
% 1.55/0.56    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f3])).
% 1.55/0.56  fof(f3,axiom,(
% 1.55/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.55/0.56  fof(f17,plain,(
% 1.55/0.56    v1_relat_1(sK1)),
% 1.55/0.56    inference(cnf_transformation,[],[f10])).
% 1.55/0.56  fof(f72,plain,(
% 1.55/0.56    r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,k1_tarski(sK0)))),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f18,f17,f59,f46])).
% 1.55/0.56  fof(f46,plain,(
% 1.55/0.56    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 1.55/0.56    inference(equality_resolution,[],[f32])).
% 1.55/0.56  fof(f32,plain,(
% 1.55/0.56    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 1.55/0.56    inference(cnf_transformation,[],[f14])).
% 1.55/0.56  fof(f14,plain,(
% 1.55/0.56    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.55/0.56    inference(flattening,[],[f13])).
% 1.55/0.56  fof(f13,plain,(
% 1.55/0.56    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.55/0.56    inference(ennf_transformation,[],[f5])).
% 1.55/0.56  fof(f5,axiom,(
% 1.55/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 1.55/0.56  fof(f59,plain,(
% 1.55/0.56    sP4(k1_funct_1(sK1,sK0),k1_tarski(sK0),sK1)),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f44,f19,f47])).
% 1.55/0.56  fof(f47,plain,(
% 1.55/0.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X1) | sP4(k1_funct_1(X0,X4),X1,X0)) )),
% 1.55/0.56    inference(equality_resolution,[],[f28])).
% 1.55/0.56  fof(f28,plain,(
% 1.55/0.56    ( ! [X4,X0,X3,X1] : (~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X1) | k1_funct_1(X0,X4) != X3 | sP4(X3,X1,X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f14])).
% 1.55/0.56  fof(f19,plain,(
% 1.55/0.56    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.55/0.56    inference(cnf_transformation,[],[f10])).
% 1.55/0.56  fof(f44,plain,(
% 1.55/0.56    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.55/0.56    inference(equality_resolution,[],[f43])).
% 1.55/0.56  fof(f43,plain,(
% 1.55/0.56    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.55/0.56    inference(equality_resolution,[],[f24])).
% 1.55/0.56  fof(f24,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.55/0.56    inference(cnf_transformation,[],[f1])).
% 1.55/0.56  fof(f18,plain,(
% 1.55/0.56    v1_funct_1(sK1)),
% 1.55/0.56    inference(cnf_transformation,[],[f10])).
% 1.55/0.56  fof(f843,plain,(
% 1.55/0.56    ~r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))),
% 1.55/0.56    inference(forward_demodulation,[],[f842,f52])).
% 1.55/0.56  fof(f842,plain,(
% 1.55/0.56    ~r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k9_relat_1(sK1,k1_tarski(sK0)))),
% 1.55/0.56    inference(subsumption_resolution,[],[f834,f270])).
% 1.55/0.56  fof(f270,plain,(
% 1.55/0.56    ~r2_hidden(k4_tarski(sK0,sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),sK1)),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f222,f64])).
% 1.55/0.56  fof(f64,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) )),
% 1.55/0.56    inference(subsumption_resolution,[],[f63,f17])).
% 1.55/0.56  fof(f63,plain,(
% 1.55/0.56    ( ! [X0,X1] : (~v1_relat_1(sK1) | k1_funct_1(sK1,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),sK1)) )),
% 1.55/0.56    inference(resolution,[],[f22,f18])).
% 1.55/0.56  fof(f22,plain,(
% 1.55/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f12])).
% 1.55/0.56  fof(f12,plain,(
% 1.55/0.56    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.55/0.56    inference(flattening,[],[f11])).
% 1.55/0.57  fof(f11,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.55/0.57    inference(ennf_transformation,[],[f6])).
% 1.55/0.57  fof(f6,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.55/0.57  fof(f222,plain,(
% 1.55/0.57    k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f20,f173,f27])).
% 1.55/0.57  fof(f834,plain,(
% 1.55/0.57    r2_hidden(k4_tarski(sK0,sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),sK1) | ~r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k9_relat_1(sK1,k1_tarski(sK0)))),
% 1.55/0.57    inference(superposition,[],[f90,f313])).
% 1.55/0.57  fof(f313,plain,(
% 1.55/0.57    sK0 = sK6(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k1_tarski(sK0),sK1)),
% 1.55/0.57    inference(unit_resulting_resolution,[],[f173,f231])).
% 1.55/0.57  fof(f231,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k11_relat_1(sK1,X1)) | sK6(X0,k1_tarski(X1),sK1) = X1) )),
% 1.55/0.57    inference(resolution,[],[f129,f42])).
% 1.55/0.57  fof(f42,plain,(
% 1.55/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.55/0.57    inference(equality_resolution,[],[f25])).
% 1.55/0.57  fof(f25,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.55/0.57    inference(cnf_transformation,[],[f1])).
% 1.55/0.57  fof(f129,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r2_hidden(sK6(X1,k1_tarski(X0),sK1),k1_tarski(X0)) | ~r2_hidden(X1,k11_relat_1(sK1,X0))) )),
% 1.55/0.57    inference(superposition,[],[f53,f52])).
% 1.55/0.57  fof(f53,plain,(
% 1.55/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK1,X1)) | r2_hidden(sK6(X0,X1,sK1),X1)) )),
% 1.55/0.57    inference(resolution,[],[f39,f17])).
% 1.55/0.57  fof(f39,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f16])).
% 1.55/0.57  fof(f16,plain,(
% 1.55/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.55/0.57    inference(ennf_transformation,[],[f4])).
% 1.55/0.57  fof(f4,axiom,(
% 1.55/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.55/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.55/0.57  fof(f90,plain,(
% 1.55/0.57    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X1,sK1),X0),sK1) | ~r2_hidden(X0,k9_relat_1(sK1,X1))) )),
% 1.55/0.57    inference(resolution,[],[f38,f17])).
% 1.55/0.57  fof(f38,plain,(
% 1.55/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 1.55/0.57    inference(cnf_transformation,[],[f16])).
% 1.55/0.57  % SZS output end Proof for theBenchmark
% 1.55/0.57  % (30173)------------------------------
% 1.55/0.57  % (30173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (30173)Termination reason: Refutation
% 1.55/0.57  
% 1.55/0.57  % (30173)Memory used [KB]: 2302
% 1.55/0.57  % (30173)Time elapsed: 0.156 s
% 1.55/0.57  % (30173)------------------------------
% 1.55/0.57  % (30173)------------------------------
% 1.55/0.57  % (30149)Success in time 0.21 s
%------------------------------------------------------------------------------
