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
% DateTime   : Thu Dec  3 12:48:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 222 expanded)
%              Number of leaves         :   10 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  148 ( 894 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2034,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2033,f159])).

fof(f159,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK2,X0)) ),
    inference(unit_resulting_resolution,[],[f25,f77,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK2) ),
    inference(unit_resulting_resolution,[],[f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f25,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
    & r1_tarski(sK0,sK1)
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f22,f21])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
            & r1_tarski(X0,X1)
            & r1_tarski(X2,X3)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
          & r1_tarski(sK0,sK1)
          & r1_tarski(sK2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
        & r1_tarski(sK0,sK1)
        & r1_tarski(sK2,X3)
        & v1_relat_1(X3) )
   => ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))
      & r1_tarski(sK0,sK1)
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          & r1_tarski(X0,X1)
          & r1_tarski(X2,X3)
          & v1_relat_1(X3) )
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ! [X3] :
            ( v1_relat_1(X3)
           => ( ( r1_tarski(X0,X1)
                & r1_tarski(X2,X3) )
             => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).

fof(f2033,plain,(
    ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f2032,f78])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK3) ),
    inference(unit_resulting_resolution,[],[f27,f38,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f27,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f2032,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK3)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f2027,f1456])).

fof(f1456,plain,(
    ! [X2] : r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK2,X2)) ),
    inference(subsumption_resolution,[],[f1450,f159])).

fof(f1450,plain,(
    ! [X2] :
      ( r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK2,X2))
      | ~ v1_relat_1(k7_relat_1(sK2,X2)) ) ),
    inference(superposition,[],[f33,f1444])).

fof(f1444,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0) ),
    inference(subsumption_resolution,[],[f108,f159])).

fof(f108,plain,(
    ! [X0] :
      ( k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)
      | ~ v1_relat_1(k7_relat_1(sK2,X0)) ) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f25,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f2027,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK0))
    | ~ r1_tarski(k7_relat_1(sK2,sK0),sK3)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f210,f246])).

fof(f246,plain,(
    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(subsumption_resolution,[],[f240,f159])).

fof(f240,plain,
    ( k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f104,f31])).

fof(f104,plain,(
    r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f28,f39,f34])).

fof(f28,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f210,plain,(
    ! [X3] :
      ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
      | ~ r1_tarski(X3,sK3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f203,f26])).

fof(f26,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f203,plain,(
    ! [X3] :
      ( ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1))
      | ~ r1_tarski(X3,sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f71,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k7_relat_1(sK3,sK1))
      | ~ r1_tarski(k7_relat_1(sK2,sK0),X0) ) ),
    inference(resolution,[],[f29,f34])).

fof(f29,plain,(
    ~ r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (6565)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.49  % (6558)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (6554)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (6574)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (6555)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (6570)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (6566)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (6552)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (6553)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (6556)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (6551)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (6572)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.51  % (6557)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (6572)Refutation not found, incomplete strategy% (6572)------------------------------
% 0.21/0.51  % (6572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6572)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6572)Memory used [KB]: 6012
% 0.21/0.51  % (6572)Time elapsed: 0.109 s
% 0.21/0.51  % (6572)------------------------------
% 0.21/0.51  % (6572)------------------------------
% 0.21/0.52  % (6562)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (6564)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (6569)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (6575)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (6567)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (6561)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (6560)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.53  % (6563)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.53  % (6571)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.53  % (6568)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.54  % (6573)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.61  % (6569)Refutation found. Thanks to Tanya!
% 0.21/0.61  % SZS status Theorem for theBenchmark
% 0.21/0.61  % SZS output start Proof for theBenchmark
% 0.21/0.61  fof(f2034,plain,(
% 0.21/0.61    $false),
% 0.21/0.61    inference(subsumption_resolution,[],[f2033,f159])).
% 0.21/0.61  fof(f159,plain,(
% 0.21/0.61    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f25,f77,f37])).
% 0.21/0.61  fof(f37,plain,(
% 0.21/0.61    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f20])).
% 0.21/0.61  fof(f20,plain,(
% 0.21/0.61    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.61    inference(ennf_transformation,[],[f3])).
% 0.21/0.61  fof(f3,axiom,(
% 0.21/0.61    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.61  fof(f77,plain,(
% 0.21/0.61    ( ! [X0] : (m1_subset_1(k7_relat_1(sK2,X0),k1_zfmisc_1(sK2))) )),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f38,f36])).
% 0.21/0.61  fof(f36,plain,(
% 0.21/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f24])).
% 0.21/0.61  fof(f24,plain,(
% 0.21/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.61    inference(nnf_transformation,[],[f2])).
% 0.21/0.61  fof(f2,axiom,(
% 0.21/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.61  fof(f38,plain,(
% 0.21/0.61    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK2)) )),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f25,f33])).
% 0.21/0.61  fof(f33,plain,(
% 0.21/0.61    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f17])).
% 0.21/0.61  fof(f17,plain,(
% 0.21/0.61    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f6])).
% 0.21/0.61  fof(f6,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.21/0.61  fof(f25,plain,(
% 0.21/0.61    v1_relat_1(sK2)),
% 0.21/0.61    inference(cnf_transformation,[],[f23])).
% 0.21/0.61  fof(f23,plain,(
% 0.21/0.61    (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 0.21/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f22,f21])).
% 0.21/0.61  fof(f21,plain,(
% 0.21/0.61    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.21/0.61    introduced(choice_axiom,[])).
% 0.21/0.61  fof(f22,plain,(
% 0.21/0.61    ? [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,X3) & v1_relat_1(X3)) => (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1)) & r1_tarski(sK0,sK1) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 0.21/0.61    introduced(choice_axiom,[])).
% 0.21/0.61  fof(f11,plain,(
% 0.21/0.61    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & r1_tarski(X0,X1) & r1_tarski(X2,X3) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.61    inference(flattening,[],[f10])).
% 0.21/0.61  fof(f10,plain,(
% 0.21/0.61    ? [X0,X1,X2] : (? [X3] : ((~r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) & (r1_tarski(X0,X1) & r1_tarski(X2,X3))) & v1_relat_1(X3)) & v1_relat_1(X2))),
% 0.21/0.61    inference(ennf_transformation,[],[f9])).
% 0.21/0.61  fof(f9,negated_conjecture,(
% 0.21/0.61    ~! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.21/0.61    inference(negated_conjecture,[],[f8])).
% 0.21/0.61  fof(f8,conjecture,(
% 0.21/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((r1_tarski(X0,X1) & r1_tarski(X2,X3)) => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_relat_1)).
% 0.21/0.61  fof(f2033,plain,(
% 0.21/0.61    ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.61    inference(subsumption_resolution,[],[f2032,f78])).
% 0.21/0.61  fof(f78,plain,(
% 0.21/0.61    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK3)) )),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f27,f38,f34])).
% 0.21/0.61  fof(f34,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f19])).
% 0.21/0.61  fof(f19,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.61    inference(flattening,[],[f18])).
% 0.21/0.61  fof(f18,plain,(
% 0.21/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.61    inference(ennf_transformation,[],[f1])).
% 0.21/0.61  fof(f1,axiom,(
% 0.21/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.61  fof(f27,plain,(
% 0.21/0.61    r1_tarski(sK2,sK3)),
% 0.21/0.61    inference(cnf_transformation,[],[f23])).
% 0.21/0.61  fof(f2032,plain,(
% 0.21/0.61    ~r1_tarski(k7_relat_1(sK2,sK0),sK3) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.61    inference(subsumption_resolution,[],[f2027,f1456])).
% 0.21/0.61  fof(f1456,plain,(
% 0.21/0.61    ( ! [X2] : (r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK2,X2))) )),
% 0.21/0.61    inference(subsumption_resolution,[],[f1450,f159])).
% 0.21/0.61  fof(f1450,plain,(
% 0.21/0.61    ( ! [X2] : (r1_tarski(k7_relat_1(sK2,X2),k7_relat_1(sK2,X2)) | ~v1_relat_1(k7_relat_1(sK2,X2))) )),
% 0.21/0.61    inference(superposition,[],[f33,f1444])).
% 0.21/0.61  fof(f1444,plain,(
% 0.21/0.61    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0)) )),
% 0.21/0.61    inference(subsumption_resolution,[],[f108,f159])).
% 0.21/0.61  fof(f108,plain,(
% 0.21/0.61    ( ! [X0] : (k7_relat_1(sK2,X0) = k7_relat_1(k7_relat_1(sK2,X0),X0) | ~v1_relat_1(k7_relat_1(sK2,X0))) )),
% 0.21/0.61    inference(resolution,[],[f39,f31])).
% 0.21/0.61  fof(f31,plain,(
% 0.21/0.61    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f15])).
% 0.21/0.61  fof(f15,plain,(
% 0.21/0.61    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(flattening,[],[f14])).
% 0.21/0.61  fof(f14,plain,(
% 0.21/0.61    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f7])).
% 0.21/0.61  fof(f7,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.61  fof(f39,plain,(
% 0.21/0.61    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) )),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f25,f32])).
% 0.21/0.61  fof(f32,plain,(
% 0.21/0.61    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f16])).
% 0.21/0.61  fof(f16,plain,(
% 0.21/0.61    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f5])).
% 0.21/0.61  fof(f5,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.21/0.61  fof(f2027,plain,(
% 0.21/0.61    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK0)) | ~r1_tarski(k7_relat_1(sK2,sK0),sK3) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.61    inference(superposition,[],[f210,f246])).
% 0.21/0.61  fof(f246,plain,(
% 0.21/0.61    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.21/0.61    inference(subsumption_resolution,[],[f240,f159])).
% 0.21/0.61  fof(f240,plain,(
% 0.21/0.61    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.21/0.61    inference(resolution,[],[f104,f31])).
% 0.21/0.61  fof(f104,plain,(
% 0.21/0.61    r1_tarski(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)),
% 0.21/0.61    inference(unit_resulting_resolution,[],[f28,f39,f34])).
% 0.21/0.61  fof(f28,plain,(
% 0.21/0.61    r1_tarski(sK0,sK1)),
% 0.21/0.61    inference(cnf_transformation,[],[f23])).
% 0.21/0.61  fof(f210,plain,(
% 0.21/0.61    ( ! [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) | ~r1_tarski(X3,sK3) | ~v1_relat_1(X3)) )),
% 0.21/0.61    inference(subsumption_resolution,[],[f203,f26])).
% 0.21/0.61  fof(f26,plain,(
% 0.21/0.61    v1_relat_1(sK3)),
% 0.21/0.61    inference(cnf_transformation,[],[f23])).
% 0.21/0.61  fof(f203,plain,(
% 0.21/0.61    ( ! [X3] : (~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(X3,sK1)) | ~r1_tarski(X3,sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(X3)) )),
% 0.21/0.61    inference(resolution,[],[f71,f30])).
% 0.21/0.61  fof(f30,plain,(
% 0.21/0.61    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.21/0.61    inference(cnf_transformation,[],[f13])).
% 0.21/0.61  fof(f13,plain,(
% 0.21/0.61    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(flattening,[],[f12])).
% 0.21/0.61  fof(f12,plain,(
% 0.21/0.61    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.21/0.61    inference(ennf_transformation,[],[f4])).
% 0.21/0.61  fof(f4,axiom,(
% 0.21/0.61    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.21/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_relat_1)).
% 0.21/0.61  fof(f71,plain,(
% 0.21/0.61    ( ! [X0] : (~r1_tarski(X0,k7_relat_1(sK3,sK1)) | ~r1_tarski(k7_relat_1(sK2,sK0),X0)) )),
% 0.21/0.61    inference(resolution,[],[f29,f34])).
% 0.21/0.61  fof(f29,plain,(
% 0.21/0.61    ~r1_tarski(k7_relat_1(sK2,sK0),k7_relat_1(sK3,sK1))),
% 0.21/0.61    inference(cnf_transformation,[],[f23])).
% 0.21/0.61  % SZS output end Proof for theBenchmark
% 0.21/0.61  % (6569)------------------------------
% 0.21/0.61  % (6569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (6569)Termination reason: Refutation
% 0.21/0.61  
% 0.21/0.61  % (6569)Memory used [KB]: 2558
% 0.21/0.61  % (6569)Time elapsed: 0.201 s
% 0.21/0.61  % (6569)------------------------------
% 0.21/0.61  % (6569)------------------------------
% 1.94/0.61  % (6547)Success in time 0.249 s
%------------------------------------------------------------------------------
