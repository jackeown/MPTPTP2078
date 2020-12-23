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
% DateTime   : Thu Dec  3 13:07:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 103 expanded)
%              Number of leaves         :   14 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 ( 264 expanded)
%              Number of equality atoms :   45 (  77 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f368,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f63,f176,f360])).

fof(f360,plain,
    ( spl3_1
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f359,f173,f60,f45])).

fof(f45,plain,
    ( spl3_1
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f60,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f173,plain,
    ( spl3_9
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f359,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f356,f175])).

fof(f175,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f356,plain,
    ( k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(k6_relat_1(sK1),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f208,f67])).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f65,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(unit_resulting_resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f208,plain,
    ( ! [X0] : k10_relat_1(k7_relat_1(k6_relat_1(sK1),X0),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) = k10_relat_1(k7_relat_1(sK0,X0),sK2)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f207,f94])).

fof(f94,plain,
    ( ! [X0,X1] : k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1)
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f88,f82])).

fof(f82,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f62,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f62,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f88,plain,
    ( ! [X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f40,f62,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f207,plain,
    ( ! [X0] : k10_relat_1(k7_relat_1(k6_relat_1(sK1),X0),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,sK2))
    | ~ spl3_9 ),
    inference(superposition,[],[f93,f175])).

fof(f93,plain,(
    ! [X2,X0,X1] : k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2) ),
    inference(forward_demodulation,[],[f90,f83])).

fof(f83,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f35])).

fof(f90,plain,(
    ! [X2,X0,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) ),
    inference(unit_resulting_resolution,[],[f40,f40,f32])).

fof(f176,plain,
    ( spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f164,f50,f173])).

fof(f50,plain,
    ( spl3_2
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f164,plain,
    ( k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f52,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)) = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(global_subsumption,[],[f41,f40,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)) = X1
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f103,f37])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

fof(f41,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f63,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f53,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f30,f45])).

fof(f30,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (10187)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.48  % (10171)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.49  % (10176)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.50  % (10168)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (10166)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (10168)Refutation not found, incomplete strategy% (10168)------------------------------
% 0.20/0.50  % (10168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10168)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (10168)Memory used [KB]: 10490
% 0.20/0.50  % (10168)Time elapsed: 0.082 s
% 0.20/0.50  % (10168)------------------------------
% 0.20/0.50  % (10168)------------------------------
% 0.20/0.50  % (10171)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f368,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f48,f53,f63,f176,f360])).
% 0.20/0.50  fof(f360,plain,(
% 0.20/0.50    spl3_1 | ~spl3_4 | ~spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f359,f173,f60,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    spl3_1 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    spl3_4 <=> v1_relat_1(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    spl3_9 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.50  fof(f359,plain,(
% 0.20/0.50    k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) | (~spl3_4 | ~spl3_9)),
% 0.20/0.50    inference(forward_demodulation,[],[f356,f175])).
% 0.20/0.50  fof(f175,plain,(
% 0.20/0.50    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) | ~spl3_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f173])).
% 0.20/0.50  fof(f356,plain,(
% 0.20/0.50    k10_relat_1(k7_relat_1(sK0,sK1),sK2) = k10_relat_1(k6_relat_1(sK1),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) | (~spl3_4 | ~spl3_9)),
% 0.20/0.50    inference(superposition,[],[f208,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f65,f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f40,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.50  fof(f208,plain,(
% 0.20/0.50    ( ! [X0] : (k10_relat_1(k7_relat_1(k6_relat_1(sK1),X0),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) = k10_relat_1(k7_relat_1(sK0,X0),sK2)) ) | (~spl3_4 | ~spl3_9)),
% 0.20/0.50    inference(forward_demodulation,[],[f207,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1)) = k10_relat_1(k7_relat_1(sK0,X0),X1)) ) | ~spl3_4),
% 0.20/0.50    inference(forward_demodulation,[],[f88,f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) ) | ~spl3_4),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f62,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    v1_relat_1(sK0) | ~spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f60])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),sK0),X1) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,X1))) ) | ~spl3_4),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f40,f62,f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    ( ! [X0] : (k10_relat_1(k7_relat_1(k6_relat_1(sK1),X0),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) = k10_relat_1(k6_relat_1(X0),k10_relat_1(sK0,sK2))) ) | ~spl3_9),
% 0.20/0.50    inference(superposition,[],[f93,f175])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2)) = k10_relat_1(k7_relat_1(k6_relat_1(X1),X0),X2)) )),
% 0.20/0.50    inference(forward_demodulation,[],[f90,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f40,f35])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),X2) = k10_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X1),X2))) )),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f40,f40,f32])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    spl3_9 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f164,f50,f173])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    spl3_2 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    k10_relat_1(sK0,sK2) = k10_relat_1(k6_relat_1(sK1),k9_relat_1(k6_relat_1(sK1),k10_relat_1(sK0,sK2))) | ~spl3_2),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f52,f106])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)) = X1 | ~r1_tarski(X1,X0)) )),
% 0.20/0.50    inference(global_subsumption,[],[f41,f40,f105])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)) = X1 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f103,f37])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),k9_relat_1(k6_relat_1(X0),X1)) = X1 | ~r1_tarski(X1,k1_relat_1(k6_relat_1(X0))) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(resolution,[],[f31,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f50])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f27,f60])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    v1_relat_1(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f25,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.50    inference(negated_conjecture,[],[f11])).
% 0.20/0.50  fof(f11,conjecture,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f29,f50])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f30,f45])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (10171)------------------------------
% 0.20/0.50  % (10171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10171)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (10171)Memory used [KB]: 10874
% 0.20/0.50  % (10171)Time elapsed: 0.022 s
% 0.20/0.50  % (10171)------------------------------
% 0.20/0.50  % (10171)------------------------------
% 0.20/0.50  % (10164)Success in time 0.145 s
%------------------------------------------------------------------------------
