%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:28 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 246 expanded)
%              Number of leaves         :    9 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  144 ( 624 expanded)
%              Number of equality atoms :   36 ( 160 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(subsumption_resolution,[],[f167,f161])).

fof(f161,plain,(
    r2_hidden(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f150])).

fof(f150,plain,
    ( sK1 != sK1
    | r2_hidden(sK3,sK1) ),
    inference(backward_demodulation,[],[f96,f144])).

fof(f144,plain,(
    sK1 = k1_relat_1(sK2) ),
    inference(resolution,[],[f140,f41])).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f140,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = k1_relat_1(sK2) ) ),
    inference(resolution,[],[f139,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f139,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_zfmisc_1(sK1))
      | sK1 = k1_relat_1(sK2) ) ),
    inference(resolution,[],[f128,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f128,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | sK1 = k1_relat_1(sK2) ),
    inference(resolution,[],[f127,f106])).

fof(f106,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK1)
    | sK1 = k1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK2),sK1)
    | sK1 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f92,f95])).

fof(f95,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f39,f22])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f92,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK1)
    | sK1 = k1_relset_1(sK1,sK0,sK2)
    | sK1 = k1_relat_1(sK2) ),
    inference(resolution,[],[f90,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f90,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2))
    | sK1 = k1_relset_1(sK1,sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK2)
    | r1_tarski(sK1,k1_relat_1(sK2))
    | r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f87,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1,X0),k1_relat_1(sK2))
      | sK1 = k1_relset_1(sK1,sK0,sK2)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f85,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | sK1 = k1_relset_1(sK1,sK0,sK2)
      | r2_hidden(X1,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f21,f44])).

fof(f44,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f21,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(X3,sK4(X3)),sK2)
      | ~ r2_hidden(X3,sK1)
      | sK1 = k1_relset_1(sK1,sK0,sK2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f127,plain,
    ( r1_tarski(k1_relat_1(sK2),sK1)
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f126,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f126,plain,
    ( r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f125,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f125,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f124,f95])).

fof(f124,plain,(
    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f40,f22])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f96,plain,
    ( r2_hidden(sK3,sK1)
    | sK1 != k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f19,f95])).

fof(f19,plain,
    ( r2_hidden(sK3,sK1)
    | sK1 != k1_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f167,plain,(
    ~ r2_hidden(sK3,sK1) ),
    inference(resolution,[],[f163,f160])).

fof(f160,plain,(
    ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2) ),
    inference(trivial_inequality_removal,[],[f151])).

fof(f151,plain,(
    ! [X4] :
      ( sK1 != sK1
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(backward_demodulation,[],[f97,f144])).

fof(f97,plain,(
    ! [X4] :
      ( sK1 != k1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(backward_demodulation,[],[f20,f95])).

fof(f20,plain,(
    ! [X4] :
      ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f163,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK7(sK2,X0)),sK2)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f43,f144])).

fof(f43,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.27/0.54  % (2280)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.55  % (2270)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.55  % (2277)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.55  % (2272)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.56  % (2278)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.50/0.56  % (2288)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.56  % (2270)Refutation found. Thanks to Tanya!
% 1.50/0.56  % SZS status Theorem for theBenchmark
% 1.50/0.56  % SZS output start Proof for theBenchmark
% 1.50/0.56  fof(f169,plain,(
% 1.50/0.56    $false),
% 1.50/0.56    inference(subsumption_resolution,[],[f167,f161])).
% 1.50/0.56  fof(f161,plain,(
% 1.50/0.56    r2_hidden(sK3,sK1)),
% 1.50/0.56    inference(trivial_inequality_removal,[],[f150])).
% 1.50/0.56  fof(f150,plain,(
% 1.50/0.56    sK1 != sK1 | r2_hidden(sK3,sK1)),
% 1.50/0.56    inference(backward_demodulation,[],[f96,f144])).
% 1.50/0.56  fof(f144,plain,(
% 1.50/0.56    sK1 = k1_relat_1(sK2)),
% 1.50/0.56    inference(resolution,[],[f140,f41])).
% 1.50/0.56  fof(f41,plain,(
% 1.50/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.56    inference(equality_resolution,[],[f26])).
% 1.50/0.56  fof(f26,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f3])).
% 1.50/0.56  fof(f3,axiom,(
% 1.50/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.56  fof(f140,plain,(
% 1.50/0.56    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = k1_relat_1(sK2)) )),
% 1.50/0.56    inference(resolution,[],[f139,f46])).
% 1.50/0.56  fof(f46,plain,(
% 1.50/0.56    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 1.50/0.56    inference(equality_resolution,[],[f35])).
% 1.50/0.56  fof(f35,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f4])).
% 1.50/0.56  fof(f4,axiom,(
% 1.50/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.50/0.56  fof(f139,plain,(
% 1.50/0.56    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(sK1)) | sK1 = k1_relat_1(sK2)) )),
% 1.50/0.56    inference(resolution,[],[f128,f23])).
% 1.50/0.56  fof(f23,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f13])).
% 1.50/0.56  fof(f13,plain,(
% 1.50/0.56    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.50/0.56    inference(ennf_transformation,[],[f11])).
% 1.50/0.56  fof(f11,plain,(
% 1.50/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.50/0.56    inference(unused_predicate_definition_removal,[],[f1])).
% 1.50/0.56  fof(f1,axiom,(
% 1.50/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.50/0.56  fof(f128,plain,(
% 1.50/0.56    v1_xboole_0(k1_zfmisc_1(sK1)) | sK1 = k1_relat_1(sK2)),
% 1.50/0.56    inference(resolution,[],[f127,f106])).
% 1.50/0.56  fof(f106,plain,(
% 1.50/0.56    ~r1_tarski(k1_relat_1(sK2),sK1) | sK1 = k1_relat_1(sK2)),
% 1.50/0.56    inference(duplicate_literal_removal,[],[f104])).
% 1.50/0.56  fof(f104,plain,(
% 1.50/0.56    sK1 = k1_relat_1(sK2) | ~r1_tarski(k1_relat_1(sK2),sK1) | sK1 = k1_relat_1(sK2)),
% 1.50/0.56    inference(backward_demodulation,[],[f92,f95])).
% 1.50/0.56  fof(f95,plain,(
% 1.50/0.56    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 1.50/0.56    inference(resolution,[],[f39,f22])).
% 1.50/0.56  fof(f22,plain,(
% 1.50/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.50/0.56    inference(cnf_transformation,[],[f12])).
% 1.50/0.56  fof(f12,plain,(
% 1.50/0.56    ? [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <~> k1_relset_1(X1,X0,X2) = X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.50/0.56    inference(ennf_transformation,[],[f10])).
% 1.50/0.56  fof(f10,negated_conjecture,(
% 1.50/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.50/0.56    inference(negated_conjecture,[],[f9])).
% 1.50/0.56  fof(f9,conjecture,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 1.50/0.56  fof(f39,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f17])).
% 1.50/0.56  fof(f17,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(ennf_transformation,[],[f8])).
% 1.50/0.56  fof(f8,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.50/0.56  fof(f92,plain,(
% 1.50/0.56    ~r1_tarski(k1_relat_1(sK2),sK1) | sK1 = k1_relset_1(sK1,sK0,sK2) | sK1 = k1_relat_1(sK2)),
% 1.50/0.56    inference(resolution,[],[f90,f27])).
% 1.50/0.56  fof(f27,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f3])).
% 1.50/0.56  fof(f90,plain,(
% 1.50/0.56    r1_tarski(sK1,k1_relat_1(sK2)) | sK1 = k1_relset_1(sK1,sK0,sK2)),
% 1.50/0.56    inference(duplicate_literal_removal,[],[f88])).
% 1.50/0.56  fof(f88,plain,(
% 1.50/0.56    sK1 = k1_relset_1(sK1,sK0,sK2) | r1_tarski(sK1,k1_relat_1(sK2)) | r1_tarski(sK1,k1_relat_1(sK2))),
% 1.50/0.56    inference(resolution,[],[f87,f30])).
% 1.50/0.56  fof(f30,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f16,plain,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.50/0.56    inference(ennf_transformation,[],[f2])).
% 1.50/0.56  fof(f2,axiom,(
% 1.50/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.50/0.56  fof(f87,plain,(
% 1.50/0.56    ( ! [X0] : (r2_hidden(sK5(sK1,X0),k1_relat_1(sK2)) | sK1 = k1_relset_1(sK1,sK0,sK2) | r1_tarski(sK1,X0)) )),
% 1.50/0.56    inference(resolution,[],[f85,f29])).
% 1.50/0.56  fof(f29,plain,(
% 1.50/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f16])).
% 1.50/0.56  fof(f85,plain,(
% 1.50/0.56    ( ! [X1] : (~r2_hidden(X1,sK1) | sK1 = k1_relset_1(sK1,sK0,sK2) | r2_hidden(X1,k1_relat_1(sK2))) )),
% 1.50/0.56    inference(resolution,[],[f21,f44])).
% 1.50/0.56  fof(f44,plain,(
% 1.50/0.56    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 1.50/0.56    inference(equality_resolution,[],[f31])).
% 1.50/0.56  fof(f31,plain,(
% 1.50/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f6])).
% 1.50/0.56  fof(f6,axiom,(
% 1.50/0.56    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.50/0.56  fof(f21,plain,(
% 1.50/0.56    ( ! [X3] : (r2_hidden(k4_tarski(X3,sK4(X3)),sK2) | ~r2_hidden(X3,sK1) | sK1 = k1_relset_1(sK1,sK0,sK2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f12])).
% 1.50/0.56  fof(f127,plain,(
% 1.50/0.56    r1_tarski(k1_relat_1(sK2),sK1) | v1_xboole_0(k1_zfmisc_1(sK1))),
% 1.50/0.56    inference(resolution,[],[f126,f45])).
% 1.50/0.56  fof(f45,plain,(
% 1.50/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.50/0.56    inference(equality_resolution,[],[f36])).
% 1.50/0.56  fof(f36,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f4])).
% 1.50/0.56  fof(f126,plain,(
% 1.50/0.56    r2_hidden(k1_relat_1(sK2),k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1))),
% 1.50/0.56    inference(resolution,[],[f125,f24])).
% 1.50/0.56  fof(f24,plain,(
% 1.50/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f15])).
% 1.50/0.56  fof(f15,plain,(
% 1.50/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.50/0.56    inference(flattening,[],[f14])).
% 1.50/0.56  fof(f14,plain,(
% 1.50/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.50/0.56    inference(ennf_transformation,[],[f5])).
% 1.50/0.56  fof(f5,axiom,(
% 1.50/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.50/0.56  fof(f125,plain,(
% 1.50/0.56    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK1))),
% 1.50/0.56    inference(forward_demodulation,[],[f124,f95])).
% 1.50/0.56  fof(f124,plain,(
% 1.50/0.56    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))),
% 1.50/0.56    inference(resolution,[],[f40,f22])).
% 1.50/0.56  fof(f40,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 1.50/0.56    inference(cnf_transformation,[],[f18])).
% 1.50/0.56  fof(f18,plain,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.50/0.56    inference(ennf_transformation,[],[f7])).
% 1.50/0.56  fof(f7,axiom,(
% 1.50/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.50/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.50/0.56  fof(f96,plain,(
% 1.50/0.56    r2_hidden(sK3,sK1) | sK1 != k1_relat_1(sK2)),
% 1.50/0.56    inference(backward_demodulation,[],[f19,f95])).
% 1.50/0.56  fof(f19,plain,(
% 1.50/0.56    r2_hidden(sK3,sK1) | sK1 != k1_relset_1(sK1,sK0,sK2)),
% 1.50/0.56    inference(cnf_transformation,[],[f12])).
% 1.50/0.56  fof(f167,plain,(
% 1.50/0.56    ~r2_hidden(sK3,sK1)),
% 1.50/0.56    inference(resolution,[],[f163,f160])).
% 1.50/0.56  fof(f160,plain,(
% 1.50/0.56    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 1.50/0.56    inference(trivial_inequality_removal,[],[f151])).
% 1.50/0.56  fof(f151,plain,(
% 1.50/0.56    ( ! [X4] : (sK1 != sK1 | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 1.50/0.56    inference(backward_demodulation,[],[f97,f144])).
% 1.50/0.56  fof(f97,plain,(
% 1.50/0.56    ( ! [X4] : (sK1 != k1_relat_1(sK2) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 1.50/0.56    inference(backward_demodulation,[],[f20,f95])).
% 1.50/0.56  fof(f20,plain,(
% 1.50/0.56    ( ! [X4] : (sK1 != k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(k4_tarski(sK3,X4),sK2)) )),
% 1.50/0.56    inference(cnf_transformation,[],[f12])).
% 1.50/0.56  fof(f163,plain,(
% 1.50/0.56    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK7(sK2,X0)),sK2) | ~r2_hidden(X0,sK1)) )),
% 1.50/0.56    inference(superposition,[],[f43,f144])).
% 1.50/0.56  fof(f43,plain,(
% 1.50/0.56    ( ! [X2,X0] : (~r2_hidden(X2,k1_relat_1(X0)) | r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)) )),
% 1.50/0.56    inference(equality_resolution,[],[f32])).
% 1.50/0.56  fof(f32,plain,(
% 1.50/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.50/0.56    inference(cnf_transformation,[],[f6])).
% 1.50/0.56  % SZS output end Proof for theBenchmark
% 1.50/0.56  % (2270)------------------------------
% 1.50/0.56  % (2270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (2270)Termination reason: Refutation
% 1.50/0.56  
% 1.50/0.56  % (2270)Memory used [KB]: 6268
% 1.50/0.56  % (2270)Time elapsed: 0.120 s
% 1.50/0.56  % (2270)------------------------------
% 1.50/0.56  % (2270)------------------------------
% 1.50/0.56  % (2263)Success in time 0.2 s
%------------------------------------------------------------------------------
