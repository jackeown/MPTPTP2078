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
% DateTime   : Thu Dec  3 12:46:50 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 229 expanded)
%              Number of leaves         :    7 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 849 expanded)
%              Number of equality atoms :    7 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1010,plain,(
    $false ),
    inference(global_subsumption,[],[f439,f1008])).

fof(f1008,plain,(
    ~ sP5(sK3(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)),sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f272,f273,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f273,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)),sK2) ),
    inference(unit_resulting_resolution,[],[f264,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,k1_zfmisc_1(sK0)),sK2)
      | r1_tarski(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f57,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
          & v3_setfam_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
              & v3_setfam_1(X1,X0) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                  & v3_setfam_1(X2,X0) )
               => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
            & v3_setfam_1(X1,X0) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
                & v3_setfam_1(X2,X0) )
             => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f264,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f138,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f138,plain,(
    ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f110,f111,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f111,plain,(
    ~ r2_hidden(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f91,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f91,plain,(
    ~ sP5(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f77,f78,f33])).

fof(f78,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f19,f20,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f77,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f16,f17,f24])).

fof(f16,plain,(
    v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f110,plain,(
    ~ v3_setfam_1(k2_xboole_0(sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f18,f101])).

fof(f101,plain,(
    k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f20,f17,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f18,plain,(
    ~ v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f272,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f264,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,k1_zfmisc_1(sK0)),sK1)
      | r1_tarski(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f58,f27])).

fof(f58,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f22,f20])).

fof(f439,plain,(
    sP5(sK3(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)),sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f264,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( sP5(sK3(k2_xboole_0(X0,X1),X2),X1,X0)
      | r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f38,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:00:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (15268)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (15285)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (15268)Refutation not found, incomplete strategy% (15268)------------------------------
% 0.21/0.51  % (15268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15277)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (15268)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15268)Memory used [KB]: 10746
% 0.21/0.51  % (15268)Time elapsed: 0.095 s
% 0.21/0.51  % (15268)------------------------------
% 0.21/0.51  % (15268)------------------------------
% 0.21/0.51  % (15257)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (15263)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (15279)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (15277)Refutation not found, incomplete strategy% (15277)------------------------------
% 0.21/0.51  % (15277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (15262)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (15277)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (15277)Memory used [KB]: 10746
% 0.21/0.51  % (15277)Time elapsed: 0.110 s
% 0.21/0.51  % (15277)------------------------------
% 0.21/0.51  % (15277)------------------------------
% 0.21/0.51  % (15271)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (15260)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (15266)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (15265)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (15269)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (15254)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (15267)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (15273)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (15258)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (15276)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (15281)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (15272)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (15259)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (15280)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (15265)Refutation not found, incomplete strategy% (15265)------------------------------
% 0.21/0.54  % (15265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15265)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15265)Memory used [KB]: 10746
% 0.21/0.54  % (15265)Time elapsed: 0.109 s
% 0.21/0.54  % (15265)------------------------------
% 0.21/0.54  % (15265)------------------------------
% 0.21/0.54  % (15286)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (15278)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (15270)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (15275)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (15282)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.55  % (15284)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % (15283)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (15267)Refutation not found, incomplete strategy% (15267)------------------------------
% 1.42/0.55  % (15267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (15267)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (15267)Memory used [KB]: 10618
% 1.42/0.55  % (15267)Time elapsed: 0.153 s
% 1.42/0.55  % (15267)------------------------------
% 1.42/0.55  % (15267)------------------------------
% 1.42/0.55  % (15274)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.55  % (15274)Refutation not found, incomplete strategy% (15274)------------------------------
% 1.42/0.55  % (15274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (15264)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.62/0.56  % (15274)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.56  
% 1.62/0.56  % (15274)Memory used [KB]: 10618
% 1.62/0.56  % (15274)Time elapsed: 0.149 s
% 1.62/0.56  % (15274)------------------------------
% 1.62/0.56  % (15274)------------------------------
% 1.62/0.57  % (15281)Refutation found. Thanks to Tanya!
% 1.62/0.57  % SZS status Theorem for theBenchmark
% 1.62/0.59  % SZS output start Proof for theBenchmark
% 1.62/0.59  fof(f1010,plain,(
% 1.62/0.59    $false),
% 1.62/0.59    inference(global_subsumption,[],[f439,f1008])).
% 1.62/0.59  fof(f1008,plain,(
% 1.62/0.59    ~sP5(sK3(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)),sK2,sK1)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f272,f273,f33])).
% 1.62/0.59  fof(f33,plain,(
% 1.62/0.59    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f2])).
% 1.62/0.59  fof(f2,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.62/0.59  fof(f273,plain,(
% 1.62/0.59    ~r2_hidden(sK3(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)),sK2)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f264,f61])).
% 1.62/0.59  fof(f61,plain,(
% 1.62/0.59    ( ! [X0] : (~r2_hidden(sK3(X0,k1_zfmisc_1(sK0)),sK2) | r1_tarski(X0,k1_zfmisc_1(sK0))) )),
% 1.62/0.59    inference(resolution,[],[f57,f27])).
% 1.62/0.59  fof(f27,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f13])).
% 1.62/0.59  fof(f13,plain,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f1])).
% 1.62/0.59  fof(f1,axiom,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.59  fof(f57,plain,(
% 1.62/0.59    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK2)) )),
% 1.62/0.59    inference(resolution,[],[f22,f17])).
% 1.62/0.59  fof(f17,plain,(
% 1.62/0.59    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.62/0.59    inference(cnf_transformation,[],[f10])).
% 1.62/0.59  fof(f10,plain,(
% 1.62/0.59    ? [X0] : (? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.62/0.59    inference(flattening,[],[f9])).
% 1.62/0.59  fof(f9,plain,(
% 1.62/0.59    ? [X0] : (? [X1] : (? [X2] : (~v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0) & (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0))) & (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0))) & ~v1_xboole_0(X0))),
% 1.62/0.59    inference(ennf_transformation,[],[f8])).
% 1.62/0.59  fof(f8,negated_conjecture,(
% 1.62/0.59    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 1.62/0.59    inference(negated_conjecture,[],[f7])).
% 1.62/0.59  fof(f7,conjecture,(
% 1.62/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X1,X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) & v3_setfam_1(X2,X0)) => v3_setfam_1(k4_subset_1(k1_zfmisc_1(X0),X1,X2),X0))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_setfam_1)).
% 1.62/0.59  fof(f22,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f11])).
% 1.62/0.59  fof(f11,plain,(
% 1.62/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f3])).
% 1.62/0.59  fof(f3,axiom,(
% 1.62/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.62/0.59  fof(f264,plain,(
% 1.62/0.59    ~r1_tarski(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f138,f28])).
% 1.62/0.59  fof(f28,plain,(
% 1.62/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f6])).
% 1.62/0.59  fof(f6,axiom,(
% 1.62/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.62/0.59  fof(f138,plain,(
% 1.62/0.59    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f110,f111,f23])).
% 1.62/0.59  fof(f23,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f12])).
% 1.62/0.59  fof(f12,plain,(
% 1.62/0.59    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.62/0.59    inference(ennf_transformation,[],[f5])).
% 1.62/0.59  fof(f5,axiom,(
% 1.62/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_setfam_1)).
% 1.62/0.59  fof(f111,plain,(
% 1.62/0.59    ~r2_hidden(sK0,k2_xboole_0(sK1,sK2))),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f91,f38])).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | sP5(X3,X1,X0)) )),
% 1.62/0.59    inference(equality_resolution,[],[f35])).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.62/0.59    inference(cnf_transformation,[],[f2])).
% 1.62/0.59  fof(f91,plain,(
% 1.62/0.59    ~sP5(sK0,sK2,sK1)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f77,f78,f33])).
% 1.62/0.59  fof(f78,plain,(
% 1.62/0.59    ~r2_hidden(sK0,sK1)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f19,f20,f24])).
% 1.62/0.59  fof(f24,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f12])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.62/0.59    inference(cnf_transformation,[],[f10])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    v3_setfam_1(sK1,sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f10])).
% 1.62/0.59  fof(f77,plain,(
% 1.62/0.59    ~r2_hidden(sK0,sK2)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f16,f17,f24])).
% 1.62/0.59  fof(f16,plain,(
% 1.62/0.59    v3_setfam_1(sK2,sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f10])).
% 1.62/0.59  fof(f110,plain,(
% 1.62/0.59    ~v3_setfam_1(k2_xboole_0(sK1,sK2),sK0)),
% 1.62/0.59    inference(backward_demodulation,[],[f18,f101])).
% 1.62/0.59  fof(f101,plain,(
% 1.62/0.59    k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f20,f17,f30])).
% 1.62/0.59  fof(f30,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f15])).
% 1.62/0.59  fof(f15,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(flattening,[],[f14])).
% 1.62/0.59  fof(f14,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.62/0.59    inference(ennf_transformation,[],[f4])).
% 1.62/0.59  fof(f4,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.62/0.59  fof(f18,plain,(
% 1.62/0.59    ~v3_setfam_1(k4_subset_1(k1_zfmisc_1(sK0),sK1,sK2),sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f10])).
% 1.62/0.59  fof(f272,plain,(
% 1.62/0.59    ~r2_hidden(sK3(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)),sK1)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f264,f65])).
% 1.62/0.59  fof(f65,plain,(
% 1.62/0.59    ( ! [X0] : (~r2_hidden(sK3(X0,k1_zfmisc_1(sK0)),sK1) | r1_tarski(X0,k1_zfmisc_1(sK0))) )),
% 1.62/0.59    inference(resolution,[],[f58,f27])).
% 1.62/0.59  fof(f58,plain,(
% 1.62/0.59    ( ! [X1] : (r2_hidden(X1,k1_zfmisc_1(sK0)) | ~r2_hidden(X1,sK1)) )),
% 1.62/0.59    inference(resolution,[],[f22,f20])).
% 1.62/0.59  fof(f439,plain,(
% 1.62/0.59    sP5(sK3(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)),sK2,sK1)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f264,f53])).
% 1.62/0.59  fof(f53,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (sP5(sK3(k2_xboole_0(X0,X1),X2),X1,X0) | r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.62/0.59    inference(resolution,[],[f38,f26])).
% 1.62/0.59  fof(f26,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f13])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (15281)------------------------------
% 1.62/0.59  % (15281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (15281)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (15281)Memory used [KB]: 7419
% 1.62/0.59  % (15281)Time elapsed: 0.173 s
% 1.62/0.59  % (15281)------------------------------
% 1.62/0.59  % (15281)------------------------------
% 1.62/0.59  % (15252)Success in time 0.225 s
%------------------------------------------------------------------------------
