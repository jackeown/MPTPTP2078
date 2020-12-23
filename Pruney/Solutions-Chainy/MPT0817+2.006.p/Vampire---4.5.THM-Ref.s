%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  78 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 217 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(subsumption_resolution,[],[f158,f39])).

fof(f39,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f37,f28])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f37,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f27,f22])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & r1_tarski(k1_relat_1(sK3),sK1)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(k1_relat_1(X3),X1)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & r1_tarski(k1_relat_1(sK3),sK1)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(k1_relat_1(X3),X1)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => ( r1_tarski(k1_relat_1(X3),X1)
         => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f158,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f155,f87])).

fof(f87,plain,(
    ~ r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(subsumption_resolution,[],[f86,f39])).

fof(f86,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f83,f23])).

fof(f23,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f83,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f20])).

% (4348)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f155,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f74,f34])).

fof(f34,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) ),
    inference(resolution,[],[f30,f22])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f74,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X3,k2_zfmisc_1(X5,X4))
      | r1_tarski(k2_relat_1(X3),X4)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f73,f28])).

fof(f73,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_relat_1(X3),X4)
      | ~ r1_tarski(X3,k2_zfmisc_1(X5,X4))
      | ~ v1_relat_1(k2_zfmisc_1(X5,X4))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f41,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f41,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X3,X2)))
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:56:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (4356)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (4358)WARNING: option uwaf not known.
% 0.21/0.50  % (4350)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.50  % (4358)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.21/0.50  % (4367)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.21/0.50  % (4367)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f158,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    v1_relat_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f37,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK2))),
% 0.21/0.51    inference(resolution,[],[f27,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(k1_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(k1_relat_1(sK3),sK1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(k1_relat_1(X3),X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ~v1_relat_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f155,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ~r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f39])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ~r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    r1_tarski(k1_relat_1(sK3),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ~r1_tarski(k2_relat_1(sK3),sK2) | ~r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f32,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  % (4348)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    r1_tarski(k2_relat_1(sK3),sK2) | ~v1_relat_1(sK3)),
% 0.21/0.51    inference(resolution,[],[f74,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))),
% 0.21/0.51    inference(resolution,[],[f30,f22])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (~r1_tarski(X3,k2_zfmisc_1(X5,X4)) | r1_tarski(k2_relat_1(X3),X4) | ~v1_relat_1(X3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f73,f28])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X4,X5,X3] : (r1_tarski(k2_relat_1(X3),X4) | ~r1_tarski(X3,k2_zfmisc_1(X5,X4)) | ~v1_relat_1(k2_zfmisc_1(X5,X4)) | ~v1_relat_1(X3)) )),
% 0.21/0.51    inference(resolution,[],[f41,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X3,X1] : (~r1_tarski(X1,k2_relat_1(k2_zfmisc_1(X3,X2))) | r1_tarski(X1,X2)) )),
% 0.21/0.51    inference(resolution,[],[f33,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t194_relat_1)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (4367)------------------------------
% 0.21/0.51  % (4367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4367)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (4367)Memory used [KB]: 5373
% 0.21/0.51  % (4367)Time elapsed: 0.078 s
% 0.21/0.51  % (4367)------------------------------
% 0.21/0.51  % (4367)------------------------------
% 0.21/0.51  % (4347)Success in time 0.147 s
%------------------------------------------------------------------------------
