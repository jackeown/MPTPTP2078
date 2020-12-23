%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:22 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 173 expanded)
%              Number of leaves         :    6 (  39 expanded)
%              Depth                    :   18
%              Number of atoms          :  161 ( 555 expanded)
%              Number of equality atoms :   25 (  77 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(subsumption_resolution,[],[f324,f60])).

fof(f60,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f59,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(sK0))
      | r1_tarski(sK1,sK0) ) ),
    inference(resolution,[],[f43,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f43,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f41,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f41,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f24,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(k1_zfmisc_1(sK0),k1_zfmisc_1(X0))
      | r1_tarski(sK1,sK0) ) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X2] :
      ( r1_tarski(k1_zfmisc_1(sK0),X2)
      | r1_tarski(sK1,sK0) ) ),
    inference(resolution,[],[f30,f46])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f324,plain,(
    ~ r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f323,f68])).

fof(f68,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f67,f37])).

fof(f67,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f323,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f314,f18])).

fof(f18,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f314,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,
    ( sK0 = sK1
    | ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | sK0 = sK1
    | ~ r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f303,f215])).

fof(f215,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X1,X0),sK0)
      | ~ r2_hidden(X1,k1_zfmisc_1(sK0))
      | X0 = X1
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f208,f79])).

fof(f79,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK1)
      | r2_hidden(X5,sK0) ) ),
    inference(resolution,[],[f29,f59])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f208,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X0,X1),sK1)
      | ~ r2_hidden(X1,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0))
      | X0 = X1 ) ),
    inference(resolution,[],[f202,f16])).

fof(f16,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK0)
      | r2_hidden(X2,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f202,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(sK3(X1,X2,X3),X1)
      | X2 = X3
      | ~ r2_hidden(X3,k1_zfmisc_1(X1))
      | ~ r2_hidden(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f160,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f23,f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f160,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(sK3(X2,X1,X3),X2)
      | X1 = X3
      | ~ r2_hidden(X3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f28,f38])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f303,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0,sK1),X0)
      | sK1 = X0
      | ~ r2_hidden(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f275,f38])).

fof(f275,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(sK0,X0,sK1),X0)
      | sK1 = X0 ) ),
    inference(subsumption_resolution,[],[f272,f172])).

fof(f172,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,X0,sK1),sK1)
      | sK1 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f159,f16])).

fof(f159,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,X0,sK1),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | sK1 = X0 ) ),
    inference(resolution,[],[f28,f17])).

fof(f272,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(sK0,X0,sK1),sK1)
      | ~ r2_hidden(sK3(sK0,X0,sK1),X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f27,f17])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:09:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (27811)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (27802)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (27805)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (27811)Refutation not found, incomplete strategy% (27811)------------------------------
% 0.21/0.51  % (27811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27811)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27811)Memory used [KB]: 10618
% 0.21/0.52  % (27811)Time elapsed: 0.107 s
% 0.21/0.52  % (27811)------------------------------
% 0.21/0.52  % (27811)------------------------------
% 0.21/0.52  % (27829)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (27818)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (27800)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (27818)Refutation not found, incomplete strategy% (27818)------------------------------
% 0.21/0.53  % (27818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27818)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27818)Memory used [KB]: 10618
% 0.21/0.53  % (27818)Time elapsed: 0.107 s
% 0.21/0.53  % (27818)------------------------------
% 0.21/0.53  % (27818)------------------------------
% 0.21/0.53  % (27812)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (27801)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (27824)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (27815)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.32/0.53  % (27806)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.53  % (27816)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.32/0.53  % (27803)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.54  % (27813)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.54  % (27821)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.54  % (27804)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (27826)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.54  % (27823)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.54  % (27828)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.54  % (27821)Refutation not found, incomplete strategy% (27821)------------------------------
% 1.32/0.54  % (27821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (27822)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.55  % (27822)Refutation not found, incomplete strategy% (27822)------------------------------
% 1.32/0.55  % (27822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (27822)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (27822)Memory used [KB]: 1663
% 1.32/0.55  % (27822)Time elapsed: 0.139 s
% 1.32/0.55  % (27822)------------------------------
% 1.32/0.55  % (27822)------------------------------
% 1.32/0.55  % (27821)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (27821)Memory used [KB]: 10746
% 1.32/0.55  % (27821)Time elapsed: 0.139 s
% 1.32/0.55  % (27821)------------------------------
% 1.32/0.55  % (27821)------------------------------
% 1.32/0.55  % (27807)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.44/0.55  % (27814)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.44/0.55  % (27820)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.55  % (27819)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.55  % (27809)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.44/0.55  % (27817)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.55  % (27808)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.55  % (27830)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.56  % (27823)Refutation not found, incomplete strategy% (27823)------------------------------
% 1.44/0.56  % (27823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (27825)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.44/0.56  % (27806)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % (27823)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (27823)Memory used [KB]: 10746
% 1.44/0.56  % (27823)Time elapsed: 0.143 s
% 1.44/0.56  % (27823)------------------------------
% 1.44/0.56  % (27823)------------------------------
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f325,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(subsumption_resolution,[],[f324,f60])).
% 1.44/0.56  fof(f60,plain,(
% 1.44/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.56    inference(resolution,[],[f59,f37])).
% 1.44/0.56  fof(f37,plain,(
% 1.44/0.56    ( ! [X2,X0] : (~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))) )),
% 1.44/0.56    inference(equality_resolution,[],[f32])).
% 1.44/0.56  fof(f32,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.44/0.56    inference(cnf_transformation,[],[f3])).
% 1.44/0.56  fof(f3,axiom,(
% 1.44/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.44/0.56  fof(f59,plain,(
% 1.44/0.56    r1_tarski(sK1,sK0)),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f58])).
% 1.44/0.56  fof(f58,plain,(
% 1.44/0.56    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 1.44/0.56    inference(resolution,[],[f56,f46])).
% 1.44/0.56  fof(f46,plain,(
% 1.44/0.56    ( ! [X2] : (~r2_hidden(X2,k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK0)) )),
% 1.44/0.56    inference(resolution,[],[f43,f20])).
% 1.44/0.56  fof(f20,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.44/0.56  fof(f43,plain,(
% 1.44/0.56    v1_xboole_0(k1_zfmisc_1(sK0)) | r1_tarski(sK1,sK0)),
% 1.44/0.56    inference(resolution,[],[f41,f36])).
% 1.44/0.56  fof(f36,plain,(
% 1.44/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.44/0.56    inference(equality_resolution,[],[f33])).
% 1.44/0.56  fof(f33,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.44/0.56    inference(cnf_transformation,[],[f3])).
% 1.44/0.56  fof(f41,plain,(
% 1.44/0.56    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.44/0.56    inference(resolution,[],[f24,f17])).
% 1.44/0.56  fof(f17,plain,(
% 1.44/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.56    inference(cnf_transformation,[],[f10])).
% 1.44/0.56  fof(f10,plain,(
% 1.44/0.56    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.56    inference(flattening,[],[f9])).
% 1.44/0.56  fof(f9,plain,(
% 1.44/0.56    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f8])).
% 1.44/0.56  fof(f8,negated_conjecture,(
% 1.44/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.44/0.56    inference(negated_conjecture,[],[f7])).
% 1.44/0.56  fof(f7,conjecture,(
% 1.44/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f11])).
% 1.44/0.56  fof(f11,plain,(
% 1.44/0.56    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f4])).
% 1.44/0.56  fof(f4,axiom,(
% 1.44/0.56    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.44/0.56  fof(f56,plain,(
% 1.44/0.56    ( ! [X0] : (r2_hidden(k1_zfmisc_1(sK0),k1_zfmisc_1(X0)) | r1_tarski(sK1,sK0)) )),
% 1.44/0.56    inference(resolution,[],[f55,f37])).
% 1.44/0.56  fof(f55,plain,(
% 1.44/0.56    ( ! [X2] : (r1_tarski(k1_zfmisc_1(sK0),X2) | r1_tarski(sK1,sK0)) )),
% 1.44/0.56    inference(resolution,[],[f30,f46])).
% 1.44/0.56  fof(f30,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f15,plain,(
% 1.44/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f2])).
% 1.44/0.56  fof(f2,axiom,(
% 1.44/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.44/0.56  fof(f324,plain,(
% 1.44/0.56    ~r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.56    inference(subsumption_resolution,[],[f323,f68])).
% 1.44/0.56  fof(f68,plain,(
% 1.44/0.56    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 1.44/0.56    inference(resolution,[],[f67,f37])).
% 1.44/0.56  fof(f67,plain,(
% 1.44/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f65])).
% 1.44/0.56  fof(f65,plain,(
% 1.44/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.44/0.56    inference(resolution,[],[f31,f30])).
% 1.44/0.56  fof(f31,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f323,plain,(
% 1.44/0.56    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.56    inference(subsumption_resolution,[],[f314,f18])).
% 1.44/0.56  fof(f18,plain,(
% 1.44/0.56    sK0 != sK1),
% 1.44/0.56    inference(cnf_transformation,[],[f10])).
% 1.44/0.56  fof(f314,plain,(
% 1.44/0.56    sK0 = sK1 | ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.56    inference(duplicate_literal_removal,[],[f309])).
% 1.44/0.56  fof(f309,plain,(
% 1.44/0.56    sK0 = sK1 | ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | sK0 = sK1 | ~r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.44/0.56    inference(resolution,[],[f303,f215])).
% 1.44/0.56  fof(f215,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X1,X0),sK0) | ~r2_hidden(X1,k1_zfmisc_1(sK0)) | X0 = X1 | ~r2_hidden(X0,k1_zfmisc_1(sK0))) )),
% 1.44/0.56    inference(resolution,[],[f208,f79])).
% 1.44/0.56  fof(f79,plain,(
% 1.44/0.56    ( ! [X5] : (~r2_hidden(X5,sK1) | r2_hidden(X5,sK0)) )),
% 1.44/0.56    inference(resolution,[],[f29,f59])).
% 1.44/0.56  fof(f29,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f15])).
% 1.44/0.56  fof(f208,plain,(
% 1.44/0.56    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),sK1) | ~r2_hidden(X1,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,k1_zfmisc_1(sK0)) | X0 = X1) )),
% 1.44/0.56    inference(resolution,[],[f202,f16])).
% 1.44/0.56  fof(f16,plain,(
% 1.44/0.56    ( ! [X2] : (~m1_subset_1(X2,sK0) | r2_hidden(X2,sK1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f10])).
% 1.44/0.56  fof(f202,plain,(
% 1.44/0.56    ( ! [X2,X3,X1] : (m1_subset_1(sK3(X1,X2,X3),X1) | X2 = X3 | ~r2_hidden(X3,k1_zfmisc_1(X1)) | ~r2_hidden(X2,k1_zfmisc_1(X1))) )),
% 1.44/0.56    inference(resolution,[],[f160,f38])).
% 1.44/0.56  fof(f38,plain,(
% 1.44/0.56    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f23,f20])).
% 1.44/0.56  fof(f23,plain,(
% 1.44/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f11])).
% 1.44/0.56  fof(f160,plain,(
% 1.44/0.56    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(sK3(X2,X1,X3),X2) | X1 = X3 | ~r2_hidden(X3,k1_zfmisc_1(X2))) )),
% 1.44/0.56    inference(resolution,[],[f28,f38])).
% 1.44/0.56  fof(f28,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | X1 = X2) )),
% 1.44/0.56    inference(cnf_transformation,[],[f14])).
% 1.44/0.56  fof(f14,plain,(
% 1.44/0.56    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.56    inference(flattening,[],[f13])).
% 1.44/0.56  fof(f13,plain,(
% 1.44/0.56    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f6])).
% 1.44/0.56  fof(f6,axiom,(
% 1.44/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.44/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 1.44/0.56  fof(f303,plain,(
% 1.44/0.56    ( ! [X0] : (~r2_hidden(sK3(sK0,X0,sK1),X0) | sK1 = X0 | ~r2_hidden(X0,k1_zfmisc_1(sK0))) )),
% 1.44/0.56    inference(resolution,[],[f275,f38])).
% 1.44/0.56  fof(f275,plain,(
% 1.44/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,X0,sK1),X0) | sK1 = X0) )),
% 1.44/0.56    inference(subsumption_resolution,[],[f272,f172])).
% 1.44/0.56  fof(f172,plain,(
% 1.44/0.56    ( ! [X0] : (r2_hidden(sK3(sK0,X0,sK1),sK1) | sK1 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 1.44/0.56    inference(resolution,[],[f159,f16])).
% 1.44/0.56  fof(f159,plain,(
% 1.44/0.56    ( ! [X0] : (m1_subset_1(sK3(sK0,X0,sK1),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | sK1 = X0) )),
% 1.44/0.56    inference(resolution,[],[f28,f17])).
% 1.44/0.56  fof(f272,plain,(
% 1.44/0.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,X0,sK1),sK1) | ~r2_hidden(sK3(sK0,X0,sK1),X0) | sK1 = X0) )),
% 1.44/0.56    inference(resolution,[],[f27,f17])).
% 1.44/0.56  fof(f27,plain,(
% 1.44/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | X1 = X2) )),
% 1.44/0.56    inference(cnf_transformation,[],[f14])).
% 1.44/0.56  % SZS output end Proof for theBenchmark
% 1.44/0.56  % (27806)------------------------------
% 1.44/0.56  % (27806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (27806)Termination reason: Refutation
% 1.44/0.56  
% 1.44/0.56  % (27806)Memory used [KB]: 6524
% 1.44/0.56  % (27806)Time elapsed: 0.136 s
% 1.44/0.56  % (27806)------------------------------
% 1.44/0.56  % (27806)------------------------------
% 1.44/0.56  % (27797)Success in time 0.199 s
%------------------------------------------------------------------------------
