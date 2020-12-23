%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:23 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   37 (  83 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   15
%              Number of atoms          :  136 ( 321 expanded)
%              Number of equality atoms :   26 (  65 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f74,plain,(
    $false ),
    inference(subsumption_resolution,[],[f73,f20])).

fof(f20,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK0 != sK1
    & ! [X2] :
        ( r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK0 != sK1
      & ! [X2] :
          ( r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ m1_subset_1(X2,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => r2_hidden(X2,X1) )
         => X0 = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).

fof(f73,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f72,f27])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f22,f21])).

fof(f21,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f72,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f71,f27])).

fof(f71,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f68,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | sK0 = sK1 ),
    inference(resolution,[],[f60,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(sK0,X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X2))
      | X0 = X1 ) ),
    inference(resolution,[],[f24,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f23,f19])).

fof(f19,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK1)
      | ~ m1_subset_1(X2,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),X0)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK2(X0,X1,X2),X2)
              | ~ r2_hidden(sK2(X0,X1,X2),X1) )
            & ( r2_hidden(sK2(X0,X1,X2),X2)
              | r2_hidden(sK2(X0,X1,X2),X1) )
            & m1_subset_1(sK2(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X2)
          | ~ r2_hidden(sK2(X0,X1,X2),X1) )
        & ( r2_hidden(sK2(X0,X1,X2),X2)
          | r2_hidden(sK2(X0,X1,X2),X1) )
        & m1_subset_1(sK2(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f60,plain,(
    ~ r2_hidden(sK2(sK0,sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f57,f20])).

fof(f57,plain,
    ( ~ r2_hidden(sK2(sK0,sK0,sK1),sK1)
    | sK0 = sK1 ),
    inference(resolution,[],[f56,f18])).

fof(f56,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(sK2(X1,X1,X2),X2)
      | X1 = X2 ) ),
    inference(subsumption_resolution,[],[f54,f23])).

fof(f54,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(sK2(X1,X1,X2),X2)
      | ~ r2_hidden(sK2(X1,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | X1 = X2 ) ),
    inference(resolution,[],[f26,f27])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:18:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (4121)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (4126)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (4110)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (4113)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (4112)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (4118)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (4114)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (4115)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.22/0.53  % (4128)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.22/0.53  % (4115)Refutation not found, incomplete strategy% (4115)------------------------------
% 1.22/0.53  % (4115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (4115)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (4115)Memory used [KB]: 6140
% 1.22/0.53  % (4115)Time elapsed: 0.103 s
% 1.22/0.53  % (4115)------------------------------
% 1.22/0.53  % (4115)------------------------------
% 1.22/0.53  % (4129)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.22/0.54  % (4125)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.22/0.54  % (4133)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.22/0.54  % (4120)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.22/0.54  % (4110)Refutation not found, incomplete strategy% (4110)------------------------------
% 1.22/0.54  % (4110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.54  % (4110)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.54  
% 1.22/0.54  % (4110)Memory used [KB]: 10618
% 1.22/0.54  % (4110)Time elapsed: 0.110 s
% 1.22/0.54  % (4110)------------------------------
% 1.22/0.54  % (4110)------------------------------
% 1.22/0.54  % (4130)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.22/0.54  % (4116)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.22/0.54  % (4131)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.22/0.54  % (4124)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.22/0.54  % (4122)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.22/0.54  % (4116)Refutation not found, incomplete strategy% (4116)------------------------------
% 1.22/0.54  % (4116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.54  % (4116)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.54  
% 1.22/0.54  % (4116)Memory used [KB]: 10618
% 1.22/0.54  % (4116)Time elapsed: 0.125 s
% 1.22/0.54  % (4116)------------------------------
% 1.22/0.54  % (4116)------------------------------
% 1.22/0.54  % (4123)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.22/0.54  % (4113)Refutation found. Thanks to Tanya!
% 1.22/0.54  % SZS status Theorem for theBenchmark
% 1.22/0.54  % SZS output start Proof for theBenchmark
% 1.22/0.54  fof(f74,plain,(
% 1.22/0.54    $false),
% 1.22/0.54    inference(subsumption_resolution,[],[f73,f20])).
% 1.22/0.54  fof(f20,plain,(
% 1.22/0.54    sK0 != sK1),
% 1.22/0.54    inference(cnf_transformation,[],[f13])).
% 1.22/0.54  fof(f13,plain,(
% 1.22/0.54    sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f12])).
% 1.22/0.54  fof(f12,plain,(
% 1.22/0.54    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK0 != sK1 & ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.22/0.54    introduced(choice_axiom,[])).
% 1.22/0.54  fof(f8,plain,(
% 1.22/0.54    ? [X0,X1] : (X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.54    inference(flattening,[],[f7])).
% 1.22/0.54  fof(f7,plain,(
% 1.22/0.54    ? [X0,X1] : ((X0 != X1 & ! [X2] : (r2_hidden(X2,X1) | ~m1_subset_1(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.54    inference(ennf_transformation,[],[f6])).
% 1.22/0.54  fof(f6,negated_conjecture,(
% 1.22/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.22/0.54    inference(negated_conjecture,[],[f5])).
% 1.22/0.54  fof(f5,conjecture,(
% 1.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_subset_1)).
% 1.22/0.54  fof(f73,plain,(
% 1.22/0.54    sK0 = sK1),
% 1.22/0.54    inference(subsumption_resolution,[],[f72,f27])).
% 1.22/0.54  fof(f27,plain,(
% 1.22/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.22/0.54    inference(forward_demodulation,[],[f22,f21])).
% 1.22/0.54  fof(f21,plain,(
% 1.22/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.22/0.54    inference(cnf_transformation,[],[f1])).
% 1.22/0.54  fof(f1,axiom,(
% 1.22/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.22/0.54  fof(f22,plain,(
% 1.22/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.22/0.54    inference(cnf_transformation,[],[f2])).
% 1.22/0.54  fof(f2,axiom,(
% 1.22/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.22/0.54  fof(f72,plain,(
% 1.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | sK0 = sK1),
% 1.22/0.54    inference(subsumption_resolution,[],[f71,f27])).
% 1.22/0.54  fof(f71,plain,(
% 1.22/0.54    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | sK0 = sK1),
% 1.22/0.54    inference(subsumption_resolution,[],[f68,f18])).
% 1.22/0.54  fof(f18,plain,(
% 1.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.22/0.54    inference(cnf_transformation,[],[f13])).
% 1.22/0.54  fof(f68,plain,(
% 1.22/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | sK0 = sK1),
% 1.22/0.54    inference(resolution,[],[f60,f29])).
% 1.22/0.54  fof(f29,plain,(
% 1.22/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK2(sK0,X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X2)) | X0 = X1) )),
% 1.22/0.54    inference(resolution,[],[f24,f28])).
% 1.22/0.54  fof(f28,plain,(
% 1.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(X1)) | r2_hidden(X0,X1)) )),
% 1.22/0.54    inference(resolution,[],[f23,f19])).
% 1.22/0.54  fof(f19,plain,(
% 1.22/0.54    ( ! [X2] : (r2_hidden(X2,sK1) | ~m1_subset_1(X2,sK0)) )),
% 1.22/0.54    inference(cnf_transformation,[],[f13])).
% 1.22/0.54  fof(f23,plain,(
% 1.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.22/0.54    inference(cnf_transformation,[],[f9])).
% 1.22/0.54  fof(f9,plain,(
% 1.22/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.54    inference(ennf_transformation,[],[f3])).
% 1.22/0.54  fof(f3,axiom,(
% 1.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.22/0.54  fof(f24,plain,(
% 1.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),X0) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.22/0.54    inference(cnf_transformation,[],[f17])).
% 1.22/0.54  fof(f17,plain,(
% 1.22/0.54    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1)) & (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1)) & m1_subset_1(sK2(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 1.22/0.54  fof(f16,plain,(
% 1.22/0.54    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1)) & (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1)) & m1_subset_1(sK2(X0,X1,X2),X0)))),
% 1.22/0.54    introduced(choice_axiom,[])).
% 1.22/0.54  fof(f15,plain,(
% 1.22/0.54    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.54    inference(flattening,[],[f14])).
% 1.22/0.54  fof(f14,plain,(
% 1.22/0.54    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.54    inference(nnf_transformation,[],[f11])).
% 1.22/0.54  fof(f11,plain,(
% 1.22/0.54    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.54    inference(flattening,[],[f10])).
% 1.22/0.54  fof(f10,plain,(
% 1.22/0.54    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.22/0.54    inference(ennf_transformation,[],[f4])).
% 1.22/0.54  fof(f4,axiom,(
% 1.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 1.22/0.54  fof(f60,plain,(
% 1.22/0.54    ~r2_hidden(sK2(sK0,sK0,sK1),sK1)),
% 1.22/0.54    inference(subsumption_resolution,[],[f57,f20])).
% 1.22/0.54  fof(f57,plain,(
% 1.22/0.54    ~r2_hidden(sK2(sK0,sK0,sK1),sK1) | sK0 = sK1),
% 1.22/0.54    inference(resolution,[],[f56,f18])).
% 1.22/0.54  fof(f56,plain,(
% 1.22/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~r2_hidden(sK2(X1,X1,X2),X2) | X1 = X2) )),
% 1.22/0.54    inference(subsumption_resolution,[],[f54,f23])).
% 1.22/0.54  fof(f54,plain,(
% 1.22/0.54    ( ! [X2,X1] : (~r2_hidden(sK2(X1,X1,X2),X2) | ~r2_hidden(sK2(X1,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | X1 = X2) )),
% 1.22/0.54    inference(resolution,[],[f26,f27])).
% 1.22/0.54  fof(f26,plain,(
% 1.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 1.22/0.54    inference(cnf_transformation,[],[f17])).
% 1.22/0.54  % SZS output end Proof for theBenchmark
% 1.22/0.54  % (4113)------------------------------
% 1.22/0.54  % (4113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.54  % (4113)Termination reason: Refutation
% 1.22/0.54  
% 1.22/0.54  % (4113)Memory used [KB]: 6140
% 1.22/0.54  % (4113)Time elapsed: 0.093 s
% 1.22/0.54  % (4113)------------------------------
% 1.22/0.54  % (4113)------------------------------
% 1.22/0.54  % (4134)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.22/0.55  % (4109)Success in time 0.18 s
%------------------------------------------------------------------------------
