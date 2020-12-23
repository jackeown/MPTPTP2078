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
% DateTime   : Thu Dec  3 13:00:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 412 expanded)
%              Number of leaves         :    7 (  81 expanded)
%              Depth                    :   17
%              Number of atoms          :  149 (1747 expanded)
%              Number of equality atoms :   40 ( 458 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(subsumption_resolution,[],[f160,f128])).

fof(f128,plain,(
    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f22,f123])).

fof(f123,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f122,f95])).

fof(f95,plain,(
    r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),sK1) ),
    inference(subsumption_resolution,[],[f92,f22])).

fof(f92,plain,
    ( r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),sK1)
    | sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(factoring,[],[f65])).

fof(f65,plain,(
    ! [X1] :
      ( r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),X1),sK1)
      | r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),X1),X1)
      | k2_relset_1(sK0,sK1,sK2) = X1 ) ),
    inference(resolution,[],[f62,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f49,f21])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X3,k2_relset_1(X1,X2,X0))
      | r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f122,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),sK1) ),
    inference(resolution,[],[f112,f17])).

fof(f17,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f112,plain,
    ( ~ r2_hidden(sK3(sK4(k2_relset_1(sK0,sK1,sK2),sK1)),sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f108,f98])).

fof(f98,plain,(
    ~ r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),k2_relset_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f96,f22])).

fof(f96,plain,
    ( ~ r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),k2_relset_1(sK0,sK1,sK2))
    | sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f95,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f108,plain,
    ( r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),k2_relset_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK1
    | ~ r2_hidden(sK3(sK4(k2_relset_1(sK0,sK1,sK2),sK1)),sK0) ),
    inference(superposition,[],[f102,f71])).

fof(f71,plain,(
    sK4(k2_relset_1(sK0,sK1,sK2),sK1) = k1_funct_1(sK2,sK3(sK4(k2_relset_1(sK0,sK1,sK2),sK1))) ),
    inference(subsumption_resolution,[],[f70,f18])).

fof(f18,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f70,plain,
    ( r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),sK1)
    | sK4(k2_relset_1(sK0,sK1,sK2),sK1) = k1_funct_1(sK2,sK3(sK4(k2_relset_1(sK0,sK1,sK2),sK1))) ),
    inference(subsumption_resolution,[],[f67,f22])).

fof(f67,plain,
    ( r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),sK1)
    | sK1 = k2_relset_1(sK0,sK1,sK2)
    | sK4(k2_relset_1(sK0,sK1,sK2),sK1) = k1_funct_1(sK2,sK3(sK4(k2_relset_1(sK0,sK1,sK2),sK1))) ),
    inference(resolution,[],[f62,f33])).

fof(f33,plain,(
    ! [X1] :
      ( r2_hidden(sK4(X1,sK1),X1)
      | sK1 = X1
      | sK4(X1,sK1) = k1_funct_1(sK2,sK3(sK4(X1,sK1))) ) ),
    inference(resolution,[],[f25,f18])).

fof(f102,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(sK0,sK1,sK2))
      | k1_xboole_0 = sK1
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f101,f20])).

fof(f20,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f50,f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(sK2,X2),k2_relset_1(X0,X1,sK2)) ) ),
    inference(resolution,[],[f29,f19])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

fof(f22,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f160,plain,(
    k1_xboole_0 = k2_relset_1(sK0,k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f159,f123])).

fof(f159,plain,(
    k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f136,f30])).

fof(f30,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f27,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f136,plain,
    ( r2_hidden(sK4(k2_relset_1(sK0,k1_xboole_0,sK2),k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f66,f123])).

fof(f66,plain,
    ( r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),k1_xboole_0),sK1)
    | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f62,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0,k1_xboole_0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f25,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:42:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (27559)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (27574)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (27560)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (27552)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (27556)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (27568)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (27553)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (27570)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (27554)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (27566)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (27581)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (27567)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (27554)Refutation not found, incomplete strategy% (27554)------------------------------
% 0.22/0.55  % (27554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27554)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27554)Memory used [KB]: 10746
% 0.22/0.55  % (27554)Time elapsed: 0.134 s
% 0.22/0.55  % (27554)------------------------------
% 0.22/0.55  % (27554)------------------------------
% 0.22/0.55  % (27563)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (27573)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (27560)Refutation not found, incomplete strategy% (27560)------------------------------
% 0.22/0.55  % (27560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27565)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (27555)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (27577)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (27558)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (27576)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (27558)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f161,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f160,f128])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2)),
% 0.22/0.55    inference(backward_demodulation,[],[f22,f123])).
% 0.22/0.55  fof(f123,plain,(
% 0.22/0.55    k1_xboole_0 = sK1),
% 0.22/0.55    inference(subsumption_resolution,[],[f122,f95])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f92,f22])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),sK1) | sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(factoring,[],[f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),X1),sK1) | r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),X1),X1) | k2_relset_1(sK0,sK1,sK2) = X1) )),
% 0.22/0.55    inference(resolution,[],[f62,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) | r2_hidden(X0,sK1)) )),
% 0.22/0.55    inference(resolution,[],[f49,f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.55    inference(negated_conjecture,[],[f7])).
% 0.22/0.55  fof(f7,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X3,k2_relset_1(X1,X2,X0)) | r2_hidden(X3,X2)) )),
% 0.22/0.55    inference(resolution,[],[f28,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | ~r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),sK1)),
% 0.22/0.55    inference(resolution,[],[f112,f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f112,plain,(
% 0.22/0.55    ~r2_hidden(sK3(sK4(k2_relset_1(sK0,sK1,sK2),sK1)),sK0) | k1_xboole_0 = sK1),
% 0.22/0.55    inference(subsumption_resolution,[],[f108,f98])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    ~r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),k2_relset_1(sK0,sK1,sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f96,f22])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ~r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),k2_relset_1(sK0,sK1,sK2)) | sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(resolution,[],[f95,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),k2_relset_1(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | ~r2_hidden(sK3(sK4(k2_relset_1(sK0,sK1,sK2),sK1)),sK0)),
% 0.22/0.55    inference(superposition,[],[f102,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    sK4(k2_relset_1(sK0,sK1,sK2),sK1) = k1_funct_1(sK2,sK3(sK4(k2_relset_1(sK0,sK1,sK2),sK1)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f70,f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),sK1) | sK4(k2_relset_1(sK0,sK1,sK2),sK1) = k1_funct_1(sK2,sK3(sK4(k2_relset_1(sK0,sK1,sK2),sK1)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f67,f22])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),sK1),sK1) | sK1 = k2_relset_1(sK0,sK1,sK2) | sK4(k2_relset_1(sK0,sK1,sK2),sK1) = k1_funct_1(sK2,sK3(sK4(k2_relset_1(sK0,sK1,sK2),sK1)))),
% 0.22/0.55    inference(resolution,[],[f62,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(sK4(X1,sK1),X1) | sK1 = X1 | sK4(X1,sK1) = k1_funct_1(sK2,sK3(sK4(X1,sK1)))) )),
% 0.22/0.55    inference(resolution,[],[f25,f18])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(sK0,sK1,sK2)) | k1_xboole_0 = sK1 | ~r2_hidden(X0,sK0)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f101,f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_funct_2(sK2,sK0,sK1) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | r2_hidden(k1_funct_1(sK2,X0),k2_relset_1(sK0,sK1,sK2))) )),
% 0.22/0.55    inference(resolution,[],[f50,f21])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(sK2,X2),k2_relset_1(X0,X1,sK2))) )),
% 0.22/0.55    inference(resolution,[],[f29,f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.55    inference(flattening,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relset_1(sK0,k1_xboole_0,sK2)),
% 0.22/0.55    inference(forward_demodulation,[],[f159,f123])).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f136,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(resolution,[],[f27,f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    r2_hidden(sK4(k2_relset_1(sK0,k1_xboole_0,sK2),k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(backward_demodulation,[],[f66,f123])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    r2_hidden(sK4(k2_relset_1(sK0,sK1,sK2),k1_xboole_0),sK1) | k1_xboole_0 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(resolution,[],[f62,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK4(X0,k1_xboole_0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(resolution,[],[f25,f30])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (27558)------------------------------
% 0.22/0.55  % (27558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (27558)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (27558)Memory used [KB]: 6268
% 0.22/0.55  % (27558)Time elapsed: 0.106 s
% 0.22/0.55  % (27558)------------------------------
% 0.22/0.55  % (27558)------------------------------
% 0.22/0.55  % (27557)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (27560)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (27560)Memory used [KB]: 10746
% 0.22/0.55  % (27560)Time elapsed: 0.134 s
% 0.22/0.55  % (27560)------------------------------
% 0.22/0.55  % (27560)------------------------------
% 0.22/0.55  % (27578)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (27574)Refutation not found, incomplete strategy% (27574)------------------------------
% 0.22/0.56  % (27574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27551)Success in time 0.191 s
%------------------------------------------------------------------------------
