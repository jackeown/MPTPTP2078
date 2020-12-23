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
% DateTime   : Thu Dec  3 13:10:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 224 expanded)
%              Number of leaves         :    5 (  39 expanded)
%              Depth                    :   25
%              Number of atoms          :  212 (1295 expanded)
%              Number of equality atoms :   49 ( 195 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(subsumption_resolution,[],[f168,f135])).

fof(f135,plain,(
    sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f134,f21])).

fof(f21,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <~> k2_lattices(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <~> k2_lattices(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_lattices(X0,X1,X2)
                <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

% (11193)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f134,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f133,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f133,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f132,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f132,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f131,f23])).

fof(f23,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f131,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f129,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f129,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v8_lattices(sK0) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( sK2 = k1_lattices(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v8_lattices(sK0)
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(superposition,[],[f26,f122])).

fof(f122,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK2)
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f121,f18])).

fof(f121,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f120,f19])).

fof(f120,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f119,f61])).

fof(f61,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f23,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f119,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK2)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f118,f20])).

fof(f118,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f16,f33])).

% (11205)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f16,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | ~ v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f10])).

% (11188)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f10,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f168,plain,(
    sK2 != k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f167,f18])).

fof(f167,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 != k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f166,f19])).

fof(f166,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 != k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f165,f61])).

fof(f165,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 != k1_lattices(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f164,f20])).

fof(f164,plain,
    ( v2_struct_0(sK0)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 != k1_lattices(sK0,sK1,sK2) ),
    inference(resolution,[],[f163,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) != X2
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f163,plain,(
    ~ r1_lattices(sK0,sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( sK1 != sK1
    | ~ r1_lattices(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f17,f160])).

fof(f160,plain,(
    sK1 = k2_lattices(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f155,f135])).

fof(f155,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2)) ),
    inference(resolution,[],[f81,f19])).

fof(f81,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_lattices(sK0,X3,k1_lattices(sK0,X3,sK2)) = X3 ) ),
    inference(subsumption_resolution,[],[f80,f22])).

fof(f22,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f80,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_lattices(sK0,X3,k1_lattices(sK0,X3,sK2)) = X3
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f23])).

fof(f79,plain,(
    ! [X3] :
      ( ~ l3_lattices(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_lattices(sK0,X3,k1_lattices(sK0,X3,sK2)) = X3
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f65,f20])).

fof(f65,plain,(
    ! [X3] :
      ( v2_struct_0(sK0)
      | ~ l3_lattices(sK0)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | k2_lattices(sK0,X3,k1_lattices(sK0,X3,sK2)) = X3
      | ~ v9_lattices(sK0) ) ),
    inference(resolution,[],[f18,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
      | ~ v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f17,plain,
    ( sK1 != k2_lattices(sK0,sK1,sK2)
    | ~ r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (11192)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (11208)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.50  % (11191)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.51  % (11190)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.51  % (11190)Refutation not found, incomplete strategy% (11190)------------------------------
% 0.20/0.51  % (11190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11187)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.51  % (11198)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (11190)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11190)Memory used [KB]: 10618
% 0.20/0.51  % (11190)Time elapsed: 0.093 s
% 0.20/0.51  % (11190)------------------------------
% 0.20/0.51  % (11190)------------------------------
% 0.20/0.51  % (11209)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.51  % (11206)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.52  % (11208)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f168,f135])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f134,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    v8_lattices(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((r1_lattices(X0,X1,X2) <~> k2_lattices(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f7])).
% 0.20/0.52  fof(f7,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((r1_lattices(X0,X1,X2) <~> k2_lattices(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.20/0.52    inference(negated_conjecture,[],[f5])).
% 0.20/0.52  fof(f5,conjecture,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 0.20/0.52  % (11193)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2) | ~v8_lattices(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f133,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v8_lattices(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f132,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v8_lattices(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f131,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    l3_lattices(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v8_lattices(sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f129,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v8_lattices(sK0)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f128])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    sK2 = k1_lattices(sK0,sK1,sK2) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~v8_lattices(sK0) | sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(superposition,[],[f26,f122])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    sK1 = k2_lattices(sK0,sK1,sK2) | sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f121,f18])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    sK1 = k2_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f120,f19])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    sK1 = k2_lattices(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f119,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    l2_lattices(sK0)),
% 0.20/0.52    inference(resolution,[],[f23,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    sK1 = k2_lattices(sK0,sK1,sK2) | ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f118,f20])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    sK1 = k2_lattices(sK0,sK1,sK2) | v2_struct_0(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 = k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(resolution,[],[f16,f33])).
% 0.20/0.52  % (11205)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    r1_lattices(sK0,sK1,sK2) | sK1 = k2_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~v8_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  % (11188)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ! [X0] : ((v8_lattices(X0) <=> ! [X1] : (! [X2] : (k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v8_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    sK2 != k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f167,f18])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 != k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f166,f19])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 != k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f165,f61])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 != k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f164,f20])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    v2_struct_0(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 != k1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(resolution,[],[f163,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) != X2 | r1_lattices(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f163,plain,(
% 0.20/0.52    ~r1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f162])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    sK1 != sK1 | ~r1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(backward_demodulation,[],[f17,f160])).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    sK1 = k2_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(forward_demodulation,[],[f155,f135])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))),
% 0.20/0.52    inference(resolution,[],[f81,f19])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,k1_lattices(sK0,X3,sK2)) = X3) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f80,f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    v9_lattices(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,k1_lattices(sK0,X3,sK2)) = X3 | ~v9_lattices(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f79,f23])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X3] : (~l3_lattices(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,k1_lattices(sK0,X3,sK2)) = X3 | ~v9_lattices(sK0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f65,f20])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X3] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,k1_lattices(sK0,X3,sK2)) = X3 | ~v9_lattices(sK0)) )),
% 0.20/0.52    inference(resolution,[],[f18,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~v9_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    sK1 != k2_lattices(sK0,sK1,sK2) | ~r1_lattices(sK0,sK1,sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (11208)------------------------------
% 0.20/0.52  % (11208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11208)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (11208)Memory used [KB]: 1663
% 0.20/0.52  % (11208)Time elapsed: 0.109 s
% 0.20/0.52  % (11208)------------------------------
% 0.20/0.52  % (11208)------------------------------
% 0.20/0.52  % (11186)Success in time 0.159 s
%------------------------------------------------------------------------------
