%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:14 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 124 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 ( 506 expanded)
%              Number of equality atoms :   24 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f55,f65,f178,f196])).

fof(f196,plain,(
    ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f184,f24])).

fof(f24,plain,(
    sK1 != k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK1 != k3_subset_1(sK0,sK2)
    & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
    & r1_xboole_0(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
            & r1_xboole_0(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != k3_subset_1(sK0,X2)
          & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
          & r1_xboole_0(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( sK1 != k3_subset_1(sK0,X2)
        & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2))
        & r1_xboole_0(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != k3_subset_1(sK0,sK2)
      & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
      & r1_xboole_0(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
          & r1_xboole_0(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
                & r1_xboole_0(X1,X2) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ( r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2))
              & r1_xboole_0(X1,X2) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).

fof(f184,plain,
    ( sK1 = k3_subset_1(sK0,sK2)
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f37,f64])).

fof(f64,plain,
    ( k3_subset_1(sK0,sK1) = sK2
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_4
  <=> k3_subset_1(sK0,sK1) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f37,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f20,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f178,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f176,f35])).

fof(f35,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f22,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f176,plain,
    ( ~ r1_xboole_0(sK2,sK1)
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f157,f60])).

fof(f60,plain,
    ( ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_3
  <=> r1_tarski(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f157,plain,
    ( r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ r1_xboole_0(sK2,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f70,f21])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(X0,k3_subset_1(sK0,sK1))
        | ~ r1_xboole_0(X0,sK1) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f68,f46])).

fof(f46,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_1
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK1)
      | r1_tarski(X0,k3_subset_1(sK0,sK1))
      | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f65,plain,
    ( ~ spl3_3
    | spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f56,f49,f62,f58])).

fof(f49,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f56,plain,
    ( k3_subset_1(sK0,sK1) = sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f51,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f55,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f53,f20])).

fof(f53,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(resolution,[],[f47,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f47,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f52,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f43,f49,f45])).

fof(f43,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f41,f21])).

fof(f41,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f23,f28])).

fof(f23,plain,(
    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (812843008)
% 0.14/0.38  ipcrm: permission denied for id (813006858)
% 0.14/0.38  ipcrm: permission denied for id (813039627)
% 0.14/0.38  ipcrm: permission denied for id (813170704)
% 0.14/0.39  ipcrm: permission denied for id (813236242)
% 0.14/0.40  ipcrm: permission denied for id (813432864)
% 0.14/0.41  ipcrm: permission denied for id (813465633)
% 0.21/0.42  ipcrm: permission denied for id (813596713)
% 0.21/0.42  ipcrm: permission denied for id (813629482)
% 0.21/0.42  ipcrm: permission denied for id (813727789)
% 0.21/0.43  ipcrm: permission denied for id (813793332)
% 0.21/0.44  ipcrm: permission denied for id (813891643)
% 0.21/0.45  ipcrm: permission denied for id (814055489)
% 0.21/0.45  ipcrm: permission denied for id (814088258)
% 0.21/0.45  ipcrm: permission denied for id (814153799)
% 0.21/0.46  ipcrm: permission denied for id (814186568)
% 0.21/0.46  ipcrm: permission denied for id (814252108)
% 0.21/0.47  ipcrm: permission denied for id (814317648)
% 0.21/0.47  ipcrm: permission denied for id (814350418)
% 0.21/0.47  ipcrm: permission denied for id (814448725)
% 0.21/0.47  ipcrm: permission denied for id (814481494)
% 0.21/0.48  ipcrm: permission denied for id (814547033)
% 0.21/0.48  ipcrm: permission denied for id (814579803)
% 0.21/0.48  ipcrm: permission denied for id (814645341)
% 0.21/0.48  ipcrm: permission denied for id (814678110)
% 0.21/0.49  ipcrm: permission denied for id (814710879)
% 0.21/0.49  ipcrm: permission denied for id (814743649)
% 0.21/0.49  ipcrm: permission denied for id (814841957)
% 0.21/0.49  ipcrm: permission denied for id (814874726)
% 0.21/0.50  ipcrm: permission denied for id (814907497)
% 0.21/0.50  ipcrm: permission denied for id (814940268)
% 0.21/0.51  ipcrm: permission denied for id (815038575)
% 0.21/0.52  ipcrm: permission denied for id (815235190)
% 0.21/0.52  ipcrm: permission denied for id (815267959)
% 0.21/0.52  ipcrm: permission denied for id (815333498)
% 0.21/0.52  ipcrm: permission denied for id (815366268)
% 1.05/0.67  % (19937)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.05/0.67  % (19939)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.05/0.67  % (19949)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.05/0.67  % (19942)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.05/0.68  % (19949)Refutation not found, incomplete strategy% (19949)------------------------------
% 1.05/0.68  % (19949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.05/0.68  % (19949)Termination reason: Refutation not found, incomplete strategy
% 1.05/0.68  
% 1.05/0.68  % (19949)Memory used [KB]: 6140
% 1.05/0.68  % (19949)Time elapsed: 0.093 s
% 1.05/0.68  % (19949)------------------------------
% 1.05/0.68  % (19949)------------------------------
% 1.05/0.68  % (19936)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.05/0.68  % (19941)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.05/0.68  % (19937)Refutation found. Thanks to Tanya!
% 1.05/0.68  % SZS status Theorem for theBenchmark
% 1.05/0.68  % (19946)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.05/0.69  % (19959)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.05/0.69  % (19957)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.05/0.69  % (19954)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.05/0.69  % (19960)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.05/0.69  % (19936)Refutation not found, incomplete strategy% (19936)------------------------------
% 1.05/0.69  % (19936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.05/0.69  % (19936)Termination reason: Refutation not found, incomplete strategy
% 1.05/0.69  
% 1.05/0.69  % (19936)Memory used [KB]: 10618
% 1.05/0.69  % (19936)Time elapsed: 0.096 s
% 1.05/0.69  % (19936)------------------------------
% 1.05/0.69  % (19936)------------------------------
% 1.05/0.69  % (19940)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.05/0.69  % (19945)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.05/0.69  % (19950)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.05/0.69  % (19944)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.05/0.69  % (19938)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.05/0.69  % (19953)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.05/0.70  % SZS output start Proof for theBenchmark
% 1.05/0.70  fof(f198,plain,(
% 1.05/0.70    $false),
% 1.05/0.70    inference(avatar_sat_refutation,[],[f52,f55,f65,f178,f196])).
% 1.05/0.70  fof(f196,plain,(
% 1.05/0.70    ~spl3_4),
% 1.05/0.70    inference(avatar_contradiction_clause,[],[f195])).
% 1.05/0.70  fof(f195,plain,(
% 1.05/0.70    $false | ~spl3_4),
% 1.05/0.70    inference(subsumption_resolution,[],[f184,f24])).
% 1.05/0.70  fof(f24,plain,(
% 1.05/0.70    sK1 != k3_subset_1(sK0,sK2)),
% 1.05/0.70    inference(cnf_transformation,[],[f16])).
% 1.05/0.70  fof(f16,plain,(
% 1.05/0.70    (sK1 != k3_subset_1(sK0,sK2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.05/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).
% 1.05/0.70  fof(f14,plain,(
% 1.05/0.70    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != k3_subset_1(sK0,X2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2)) & r1_xboole_0(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.05/0.70    introduced(choice_axiom,[])).
% 1.05/0.70  fof(f15,plain,(
% 1.05/0.70    ? [X2] : (sK1 != k3_subset_1(sK0,X2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X2)) & r1_xboole_0(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != k3_subset_1(sK0,sK2) & r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) & r1_xboole_0(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.05/0.70    introduced(choice_axiom,[])).
% 1.05/0.70  fof(f9,plain,(
% 1.05/0.70    ? [X0,X1] : (? [X2] : (k3_subset_1(X0,X2) != X1 & r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.05/0.70    inference(flattening,[],[f8])).
% 1.05/0.70  fof(f8,plain,(
% 1.05/0.70    ? [X0,X1] : (? [X2] : ((k3_subset_1(X0,X2) != X1 & (r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.05/0.70    inference(ennf_transformation,[],[f7])).
% 1.05/0.70  fof(f7,negated_conjecture,(
% 1.05/0.70    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 1.05/0.70    inference(negated_conjecture,[],[f6])).
% 1.05/0.70  fof(f6,conjecture,(
% 1.05/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_xboole_0(k3_subset_1(X0,X1),k3_subset_1(X0,X2)) & r1_xboole_0(X1,X2)) => k3_subset_1(X0,X2) = X1)))),
% 1.05/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_subset_1)).
% 1.05/0.70  fof(f184,plain,(
% 1.05/0.70    sK1 = k3_subset_1(sK0,sK2) | ~spl3_4),
% 1.05/0.70    inference(backward_demodulation,[],[f37,f64])).
% 1.05/0.70  fof(f64,plain,(
% 1.05/0.70    k3_subset_1(sK0,sK1) = sK2 | ~spl3_4),
% 1.05/0.70    inference(avatar_component_clause,[],[f62])).
% 1.05/0.70  fof(f62,plain,(
% 1.05/0.70    spl3_4 <=> k3_subset_1(sK0,sK1) = sK2),
% 1.05/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.05/0.70  fof(f37,plain,(
% 1.05/0.70    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.05/0.70    inference(resolution,[],[f20,f27])).
% 1.05/0.70  fof(f27,plain,(
% 1.05/0.70    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.05/0.70    inference(cnf_transformation,[],[f12])).
% 1.05/0.70  fof(f12,plain,(
% 1.05/0.70    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.05/0.70    inference(ennf_transformation,[],[f4])).
% 1.05/0.70  fof(f4,axiom,(
% 1.05/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.05/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.05/0.70  fof(f20,plain,(
% 1.05/0.70    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.05/0.70    inference(cnf_transformation,[],[f16])).
% 1.05/0.70  fof(f178,plain,(
% 1.05/0.70    ~spl3_1 | spl3_3),
% 1.05/0.70    inference(avatar_contradiction_clause,[],[f177])).
% 1.05/0.70  fof(f177,plain,(
% 1.05/0.70    $false | (~spl3_1 | spl3_3)),
% 1.05/0.70    inference(subsumption_resolution,[],[f176,f35])).
% 1.05/0.70  fof(f35,plain,(
% 1.05/0.70    r1_xboole_0(sK2,sK1)),
% 1.05/0.70    inference(resolution,[],[f22,f25])).
% 1.05/0.70  fof(f25,plain,(
% 1.05/0.70    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.05/0.70    inference(cnf_transformation,[],[f10])).
% 1.05/0.70  fof(f10,plain,(
% 1.05/0.70    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.05/0.70    inference(ennf_transformation,[],[f1])).
% 1.05/0.70  fof(f1,axiom,(
% 1.05/0.70    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.05/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.05/0.70  fof(f22,plain,(
% 1.05/0.70    r1_xboole_0(sK1,sK2)),
% 1.05/0.70    inference(cnf_transformation,[],[f16])).
% 1.05/0.70  fof(f176,plain,(
% 1.05/0.70    ~r1_xboole_0(sK2,sK1) | (~spl3_1 | spl3_3)),
% 1.05/0.70    inference(subsumption_resolution,[],[f157,f60])).
% 1.05/0.70  fof(f60,plain,(
% 1.05/0.70    ~r1_tarski(sK2,k3_subset_1(sK0,sK1)) | spl3_3),
% 1.05/0.70    inference(avatar_component_clause,[],[f58])).
% 1.05/0.70  fof(f58,plain,(
% 1.05/0.70    spl3_3 <=> r1_tarski(sK2,k3_subset_1(sK0,sK1))),
% 1.05/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.05/0.70  fof(f157,plain,(
% 1.05/0.70    r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~r1_xboole_0(sK2,sK1) | ~spl3_1),
% 1.05/0.70    inference(resolution,[],[f70,f21])).
% 1.05/0.70  fof(f21,plain,(
% 1.05/0.70    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.05/0.70    inference(cnf_transformation,[],[f16])).
% 1.05/0.70  fof(f70,plain,(
% 1.05/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,k3_subset_1(sK0,sK1)) | ~r1_xboole_0(X0,sK1)) ) | ~spl3_1),
% 1.05/0.70    inference(subsumption_resolution,[],[f68,f46])).
% 1.05/0.70  fof(f46,plain,(
% 1.05/0.70    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.05/0.70    inference(avatar_component_clause,[],[f45])).
% 1.05/0.70  fof(f45,plain,(
% 1.05/0.70    spl3_1 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.05/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.05/0.70  fof(f68,plain,(
% 1.05/0.70    ( ! [X0] : (~r1_xboole_0(X0,sK1) | r1_tarski(X0,k3_subset_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 1.05/0.70    inference(superposition,[],[f28,f37])).
% 1.05/0.70  fof(f28,plain,(
% 1.05/0.70    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,k3_subset_1(X0,X2)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.05/0.70    inference(cnf_transformation,[],[f17])).
% 1.05/0.70  fof(f17,plain,(
% 1.05/0.70    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.05/0.70    inference(nnf_transformation,[],[f13])).
% 1.05/0.70  fof(f13,plain,(
% 1.05/0.70    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.05/0.70    inference(ennf_transformation,[],[f5])).
% 1.05/0.70  fof(f5,axiom,(
% 1.05/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 1.05/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).
% 1.05/0.70  fof(f65,plain,(
% 1.05/0.70    ~spl3_3 | spl3_4 | ~spl3_2),
% 1.05/0.70    inference(avatar_split_clause,[],[f56,f49,f62,f58])).
% 1.05/0.70  fof(f49,plain,(
% 1.05/0.70    spl3_2 <=> r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 1.05/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.05/0.70  fof(f56,plain,(
% 1.05/0.70    k3_subset_1(sK0,sK1) = sK2 | ~r1_tarski(sK2,k3_subset_1(sK0,sK1)) | ~spl3_2),
% 1.05/0.70    inference(resolution,[],[f51,f32])).
% 1.05/0.70  fof(f32,plain,(
% 1.05/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.05/0.70    inference(cnf_transformation,[],[f19])).
% 1.05/0.70  fof(f19,plain,(
% 1.05/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.05/0.70    inference(flattening,[],[f18])).
% 1.05/0.70  fof(f18,plain,(
% 1.05/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.05/0.70    inference(nnf_transformation,[],[f2])).
% 1.05/0.70  fof(f2,axiom,(
% 1.05/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.05/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.05/0.70  fof(f51,plain,(
% 1.05/0.70    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~spl3_2),
% 1.05/0.70    inference(avatar_component_clause,[],[f49])).
% 1.05/0.70  fof(f55,plain,(
% 1.05/0.70    spl3_1),
% 1.05/0.70    inference(avatar_contradiction_clause,[],[f54])).
% 1.05/0.70  fof(f54,plain,(
% 1.05/0.70    $false | spl3_1),
% 1.05/0.70    inference(subsumption_resolution,[],[f53,f20])).
% 1.05/0.70  fof(f53,plain,(
% 1.05/0.70    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_1),
% 1.05/0.70    inference(resolution,[],[f47,f26])).
% 1.05/0.70  fof(f26,plain,(
% 1.05/0.70    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.05/0.70    inference(cnf_transformation,[],[f11])).
% 1.05/0.70  fof(f11,plain,(
% 1.05/0.70    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.05/0.70    inference(ennf_transformation,[],[f3])).
% 1.05/0.70  fof(f3,axiom,(
% 1.05/0.70    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.05/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.05/0.70  fof(f47,plain,(
% 1.05/0.70    ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl3_1),
% 1.05/0.70    inference(avatar_component_clause,[],[f45])).
% 1.05/0.70  fof(f52,plain,(
% 1.05/0.70    ~spl3_1 | spl3_2),
% 1.05/0.70    inference(avatar_split_clause,[],[f43,f49,f45])).
% 1.05/0.70  fof(f43,plain,(
% 1.05/0.70    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.05/0.70    inference(subsumption_resolution,[],[f41,f21])).
% 1.05/0.70  fof(f41,plain,(
% 1.05/0.70    r1_tarski(k3_subset_1(sK0,sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.05/0.70    inference(resolution,[],[f23,f28])).
% 1.05/0.70  fof(f23,plain,(
% 1.05/0.70    r1_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))),
% 1.05/0.70    inference(cnf_transformation,[],[f16])).
% 1.05/0.70  % SZS output end Proof for theBenchmark
% 1.05/0.70  % (19937)------------------------------
% 1.05/0.70  % (19937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.05/0.70  % (19937)Termination reason: Refutation
% 1.05/0.70  
% 1.05/0.70  % (19937)Memory used [KB]: 10618
% 1.05/0.70  % (19937)Time elapsed: 0.096 s
% 1.05/0.70  % (19937)------------------------------
% 1.05/0.70  % (19937)------------------------------
% 1.05/0.70  % (19943)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.05/0.70  % (19951)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.05/0.70  % (19757)Success in time 0.337 s
%------------------------------------------------------------------------------
