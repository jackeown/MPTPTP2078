%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 120 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :  196 ( 628 expanded)
%              Number of equality atoms :   29 (  93 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7468)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f1447,plain,(
    $false ),
    inference(global_subsumption,[],[f19,f20,f88,f1444])).

fof(f1444,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(k5_relat_1(sK0,sK1)) = k4_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f1439,f22])).

fof(f22,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          & v2_funct_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( v2_funct_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(f1439,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(sK0,X0)) = k2_funct_1(k5_relat_1(sK0,X0)) ) ),
    inference(global_subsumption,[],[f24,f25,f1431])).

% (7471)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% (7483)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f1431,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(sK0,X0)) = k2_funct_1(k5_relat_1(sK0,X0)) ) ),
    inference(resolution,[],[f380,f21])).

fof(f21,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f380,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X1,X0)) = k2_funct_1(k5_relat_1(X1,X0)) ) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X1,X0)) = k2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f153,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

% (7463)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f153,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X1,X0)) = k2_funct_1(k5_relat_1(X1,X0)) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | k4_relat_1(k5_relat_1(X1,X0)) = k2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | k4_relat_1(k5_relat_1(X0,X1)) = k2_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v2_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => v2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,(
    k2_funct_1(k5_relat_1(sK0,sK1)) != k4_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f37,f46])).

fof(f46,plain,(
    k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f38,f24])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,sK1)) = k5_relat_1(k4_relat_1(sK1),k4_relat_1(X0)) ) ),
    inference(resolution,[],[f26,f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f37,plain,(
    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f36,f35])).

fof(f35,plain,(
    k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(global_subsumption,[],[f19,f20,f33])).

fof(f33,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k2_funct_1(sK1) = k4_relat_1(sK1) ),
    inference(resolution,[],[f27,f22])).

fof(f36,plain,(
    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k2_funct_1(sK1),k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f23,f34])).

fof(f34,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(global_subsumption,[],[f24,f25,f32])).

fof(f32,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f27,f21])).

fof(f23,plain,(
    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (7474)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (7466)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.48  % (7472)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.48  % (7472)Refutation not found, incomplete strategy% (7472)------------------------------
% 0.21/0.48  % (7472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7472)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7472)Memory used [KB]: 10618
% 0.21/0.48  % (7472)Time elapsed: 0.086 s
% 0.21/0.48  % (7472)------------------------------
% 0.21/0.48  % (7472)------------------------------
% 0.21/0.49  % (7484)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.49  % (7469)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (7480)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (7476)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (7464)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (7467)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (7474)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (7470)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (7473)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (7477)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  % (7468)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  fof(f1447,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(global_subsumption,[],[f19,f20,f88,f1444])).
% 0.21/0.51  fof(f1444,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(k5_relat_1(sK0,sK1)) = k4_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f1439,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) & v2_funct_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) != k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) & (v2_funct_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f6])).
% 0.21/0.51  fof(f6,conjecture,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).
% 0.21/0.51  fof(f1439,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(sK0,X0)) = k2_funct_1(k5_relat_1(sK0,X0))) )),
% 0.21/0.51    inference(global_subsumption,[],[f24,f25,f1431])).
% 0.21/0.51  % (7471)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  % (7483)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  fof(f1431,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(sK0,X0)) = k2_funct_1(k5_relat_1(sK0,X0))) )),
% 0.21/0.51    inference(resolution,[],[f380,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    v2_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X1,X0)) = k2_funct_1(k5_relat_1(X1,X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f363])).
% 0.21/0.51  fof(f363,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X1,X0)) = k2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f153,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.51  % (7463)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X1,X0)) = k2_funct_1(k5_relat_1(X1,X0))) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f146])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(k5_relat_1(X1,X0)) | k4_relat_1(k5_relat_1(X1,X0)) = k2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f48,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v2_funct_1(X1) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(k5_relat_1(X0,X1)) | k4_relat_1(k5_relat_1(X0,X1)) = k2_funct_1(k5_relat_1(X0,X1))) )),
% 0.21/0.51    inference(resolution,[],[f28,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v2_funct_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => v2_funct_1(k5_relat_1(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_1)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    v1_funct_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    v1_relat_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    k2_funct_1(k5_relat_1(sK0,sK1)) != k4_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(backward_demodulation,[],[f37,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,sK1))),
% 0.21/0.51    inference(resolution,[],[f38,f24])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,sK1)) = k5_relat_1(k4_relat_1(sK1),k4_relat_1(X0))) )),
% 0.21/0.51    inference(resolution,[],[f26,f19])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k4_relat_1(sK1),k4_relat_1(sK0))),
% 0.21/0.51    inference(backward_demodulation,[],[f36,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.21/0.51    inference(global_subsumption,[],[f19,f20,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | k2_funct_1(sK1) = k4_relat_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f27,f22])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k2_funct_1(sK1),k4_relat_1(sK0))),
% 0.21/0.51    inference(backward_demodulation,[],[f23,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.51    inference(global_subsumption,[],[f24,f25,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f27,f21])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    k2_funct_1(k5_relat_1(sK0,sK1)) != k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    v1_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    v1_relat_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (7474)------------------------------
% 0.21/0.51  % (7474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7474)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (7474)Memory used [KB]: 12920
% 0.21/0.51  % (7474)Time elapsed: 0.099 s
% 0.21/0.51  % (7474)------------------------------
% 0.21/0.51  % (7474)------------------------------
% 0.21/0.51  % (7461)Success in time 0.162 s
%------------------------------------------------------------------------------
