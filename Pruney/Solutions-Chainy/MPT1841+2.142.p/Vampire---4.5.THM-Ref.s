%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:28 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 104 expanded)
%              Number of leaves         :   12 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 280 expanded)
%              Number of equality atoms :   32 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(subsumption_resolution,[],[f116,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f116,plain,(
    ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f54,f107])).

fof(f107,plain,(
    k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f102,f52])).

fof(f52,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f30,f38])).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f30,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f102,plain,
    ( v1_subset_1(sK0,sK0)
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(superposition,[],[f72,f84])).

fof(f84,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = k2_tarski(sK1,sK1) ),
    inference(resolution,[],[f81,f70])).

fof(f70,plain,(
    r1_tarski(k2_tarski(sK1,sK1),sK0) ),
    inference(backward_demodulation,[],[f61,f66])).

fof(f66,plain,(
    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f28,f25,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f32,f43])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f25,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f28,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    r1_tarski(k6_domain_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f60,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f60,plain,(
    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f28,f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | sK0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK0)
      | sK0 = X0 ) ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f62,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f29,f27])).

fof(f27,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f72,plain,(
    v1_subset_1(k2_tarski(sK1,sK1),sK0) ),
    inference(backward_demodulation,[],[f26,f66])).

fof(f26,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0] : ~ r1_tarski(k2_tarski(X0,X0),X0) ),
    inference(unit_resulting_resolution,[],[f51,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f51,plain,(
    ! [X2] : r2_hidden(X2,k2_tarski(X2,X2)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_tarski(X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.31/0.53  % (18069)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.53  % (18085)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.54  % (18077)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.55  % (18068)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.55  % (18077)Refutation found. Thanks to Tanya!
% 1.31/0.55  % SZS status Theorem for theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f119,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(subsumption_resolution,[],[f116,f37])).
% 1.50/0.56  fof(f37,plain,(
% 1.50/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.50/0.56  fof(f116,plain,(
% 1.50/0.56    ~r1_tarski(k1_xboole_0,sK1)),
% 1.50/0.56    inference(superposition,[],[f54,f107])).
% 1.50/0.56  fof(f107,plain,(
% 1.50/0.56    k1_xboole_0 = k2_tarski(sK1,sK1)),
% 1.50/0.56    inference(subsumption_resolution,[],[f102,f52])).
% 1.50/0.56  fof(f52,plain,(
% 1.50/0.56    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.50/0.56    inference(backward_demodulation,[],[f30,f38])).
% 1.50/0.56  fof(f38,plain,(
% 1.50/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f6])).
% 1.50/0.56  fof(f6,axiom,(
% 1.50/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.50/0.56  fof(f30,plain,(
% 1.50/0.56    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,axiom,(
% 1.50/0.56    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).
% 1.50/0.56  fof(f102,plain,(
% 1.50/0.56    v1_subset_1(sK0,sK0) | k1_xboole_0 = k2_tarski(sK1,sK1)),
% 1.50/0.56    inference(superposition,[],[f72,f84])).
% 1.50/0.56  fof(f84,plain,(
% 1.50/0.56    sK0 = k2_tarski(sK1,sK1) | k1_xboole_0 = k2_tarski(sK1,sK1)),
% 1.50/0.56    inference(resolution,[],[f81,f70])).
% 1.50/0.56  fof(f70,plain,(
% 1.50/0.56    r1_tarski(k2_tarski(sK1,sK1),sK0)),
% 1.50/0.56    inference(backward_demodulation,[],[f61,f66])).
% 1.50/0.56  fof(f66,plain,(
% 1.50/0.56    k6_domain_1(sK0,sK1) = k2_tarski(sK1,sK1)),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f28,f25,f44])).
% 1.50/0.56  fof(f44,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 1.50/0.56    inference(definition_unfolding,[],[f32,f43])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f22])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.50/0.56    inference(flattening,[],[f21])).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,axiom,(
% 1.50/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.50/0.56  fof(f25,plain,(
% 1.50/0.56    m1_subset_1(sK1,sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f16,plain,(
% 1.50/0.56    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.50/0.56    inference(flattening,[],[f15])).
% 1.50/0.56  fof(f15,plain,(
% 1.50/0.56    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f14])).
% 1.50/0.56  fof(f14,negated_conjecture,(
% 1.50/0.56    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.50/0.56    inference(negated_conjecture,[],[f13])).
% 1.50/0.56  fof(f13,conjecture,(
% 1.50/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 1.50/0.56  fof(f28,plain,(
% 1.50/0.56    ~v1_xboole_0(sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f61,plain,(
% 1.50/0.56    r1_tarski(k6_domain_1(sK0,sK1),sK0)),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f60,f34])).
% 1.50/0.56  fof(f34,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f8])).
% 1.50/0.56  fof(f8,axiom,(
% 1.50/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.50/0.56  fof(f60,plain,(
% 1.50/0.56    m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f28,f25,f31])).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f20])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.50/0.56    inference(flattening,[],[f19])).
% 1.50/0.56  fof(f19,plain,(
% 1.50/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,axiom,(
% 1.50/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.50/0.56  fof(f81,plain,(
% 1.50/0.56    ( ! [X0] : (~r1_tarski(X0,sK0) | sK0 = X0 | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(resolution,[],[f63,f35])).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.50/0.56    inference(cnf_transformation,[],[f23])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.50/0.56  fof(f63,plain,(
% 1.50/0.56    ( ! [X0] : (v1_xboole_0(X0) | ~r1_tarski(X0,sK0) | sK0 = X0) )),
% 1.50/0.56    inference(subsumption_resolution,[],[f62,f28])).
% 1.50/0.56  fof(f62,plain,(
% 1.50/0.56    ( ! [X0] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | ~r1_tarski(X0,sK0) | sK0 = X0) )),
% 1.50/0.56    inference(resolution,[],[f29,f27])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    v1_zfmisc_1(sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f18,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.50/0.56    inference(flattening,[],[f17])).
% 1.50/0.56  fof(f17,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f12])).
% 1.50/0.56  fof(f12,axiom,(
% 1.50/0.56    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.50/0.56  fof(f72,plain,(
% 1.50/0.56    v1_subset_1(k2_tarski(sK1,sK1),sK0)),
% 1.50/0.56    inference(backward_demodulation,[],[f26,f66])).
% 1.50/0.56  fof(f26,plain,(
% 1.50/0.56    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f54,plain,(
% 1.50/0.56    ( ! [X0] : (~r1_tarski(k2_tarski(X0,X0),X0)) )),
% 1.50/0.56    inference(unit_resulting_resolution,[],[f51,f36])).
% 1.50/0.56  fof(f36,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f24])).
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f9])).
% 1.50/0.56  fof(f9,axiom,(
% 1.50/0.56    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.50/0.56  fof(f51,plain,(
% 1.50/0.56    ( ! [X2] : (r2_hidden(X2,k2_tarski(X2,X2))) )),
% 1.50/0.56    inference(equality_resolution,[],[f50])).
% 1.50/0.56  fof(f50,plain,(
% 1.50/0.56    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_tarski(X2,X2) != X1) )),
% 1.50/0.56    inference(equality_resolution,[],[f48])).
% 1.50/0.56  fof(f48,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 1.50/0.56    inference(definition_unfolding,[],[f39,f43])).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (18077)------------------------------
% 1.50/0.56  % (18077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (18077)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (18077)Memory used [KB]: 1791
% 1.50/0.56  % (18077)Time elapsed: 0.134 s
% 1.50/0.56  % (18077)------------------------------
% 1.50/0.56  % (18077)------------------------------
% 1.50/0.56  % (18057)Success in time 0.2 s
%------------------------------------------------------------------------------
