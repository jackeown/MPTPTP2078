%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 128 expanded)
%              Number of leaves         :   16 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  200 ( 664 expanded)
%              Number of equality atoms :   63 ( 270 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f37,f41,f45,f49,f53,f59,f127,f133])).

fof(f133,plain,
    ( ~ spl4_5
    | spl4_1
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f129,f125,f27,f43])).

fof(f43,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f27,plain,
    ( spl4_1
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f125,plain,
    ( spl4_19
  <=> sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f129,plain,
    ( sK1 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl4_19 ),
    inference(superposition,[],[f23,f126])).

fof(f126,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f127,plain,
    ( spl4_19
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f123,f57,f51,f47,f43,f35,f31,f125])).

fof(f31,plain,
    ( spl4_2
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f35,plain,
    ( spl4_3
  <=> k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f47,plain,
    ( spl4_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f51,plain,
    ( spl4_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f57,plain,
    ( spl4_8
  <=> sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f123,plain,
    ( sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f122,f58])).

fof(f58,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f122,plain,
    ( k5_relat_1(sK1,k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f113,f36])).

fof(f36,plain,
    ( k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f113,plain,
    ( k5_relat_1(sK1,k6_relat_1(sK0)) = k5_relat_1(k5_relat_1(sK1,sK2),sK3)
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(resolution,[],[f66,f52])).

fof(f52,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f66,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(X1,sK2),sK3) = k5_relat_1(X1,k6_relat_1(sK0)) )
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f64,f32])).

fof(f32,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f64,plain,
    ( ! [X1] :
        ( k5_relat_1(k5_relat_1(X1,sK2),sK3) = k5_relat_1(X1,k5_relat_1(sK2,sK3))
        | ~ v1_relat_1(X1) )
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f60,f48])).

fof(f48,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(k5_relat_1(X0,X1),sK3) = k5_relat_1(X0,k5_relat_1(X1,sK3))
        | ~ v1_relat_1(X0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f24,f44])).

fof(f44,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f59,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f54,f39,f57,f51])).

fof(f39,plain,
    ( spl4_4
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f54,plain,
    ( sK1 = k5_relat_1(sK1,k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f25,f40])).

fof(f40,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f53,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f16,f51])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK1 != sK3
    & k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))
    & r1_tarski(k2_relat_1(sK1),sK0)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( X1 != X3
                & k6_relat_1(X0) = k5_relat_1(X2,X3)
                & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                & r1_tarski(k2_relat_1(X1),X0)
                & v1_relat_1(X3) )
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( sK1 != X3
              & k5_relat_1(X2,X3) = k6_relat_1(sK0)
              & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2)
              & r1_tarski(k2_relat_1(sK1),sK0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( sK1 != X3
            & k5_relat_1(X2,X3) = k6_relat_1(sK0)
            & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2)
            & r1_tarski(k2_relat_1(sK1),sK0)
            & v1_relat_1(X3) )
        & v1_relat_1(X2) )
   => ( ? [X3] :
          ( sK1 != X3
          & k6_relat_1(sK0) = k5_relat_1(sK2,X3)
          & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2)
          & r1_tarski(k2_relat_1(sK1),sK0)
          & v1_relat_1(X3) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X3] :
        ( sK1 != X3
        & k6_relat_1(sK0) = k5_relat_1(sK2,X3)
        & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2)
        & r1_tarski(k2_relat_1(sK1),sK0)
        & v1_relat_1(X3) )
   => ( sK1 != sK3
      & k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
      & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))
      & r1_tarski(k2_relat_1(sK1),sK0)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( X1 != X3
              & k6_relat_1(X0) = k5_relat_1(X2,X3)
              & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
              & r1_tarski(k2_relat_1(X1),X0)
              & v1_relat_1(X3) )
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ! [X3] :
                ( v1_relat_1(X3)
               => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                    & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                    & r1_tarski(k2_relat_1(X1),X0) )
                 => X1 = X3 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( v1_relat_1(X3)
             => ( ( k6_relat_1(X0) = k5_relat_1(X2,X3)
                  & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3))
                  & r1_tarski(k2_relat_1(X1),X0) )
               => X1 = X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_relat_1)).

fof(f49,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f17,f47])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f45,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f31])).

fof(f21,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f29,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f27])).

fof(f22,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (24474)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (24480)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (24465)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (24466)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (24462)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (24466)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f29,f33,f37,f41,f45,f49,f53,f59,f127,f133])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    ~spl4_5 | spl4_1 | ~spl4_19),
% 0.20/0.48    inference(avatar_split_clause,[],[f129,f125,f27,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    spl4_5 <=> v1_relat_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    spl4_1 <=> sK1 = sK3),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    spl4_19 <=> sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    sK1 = sK3 | ~v1_relat_1(sK3) | ~spl4_19),
% 0.20/0.48    inference(superposition,[],[f23,f126])).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) | ~spl4_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f125])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    spl4_19 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f123,f57,f51,f47,f43,f35,f31,f125])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    spl4_2 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    spl4_3 <=> k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl4_6 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl4_7 <=> v1_relat_1(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl4_8 <=> sK1 = k5_relat_1(sK1,k6_relat_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) | (~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 0.20/0.48    inference(forward_demodulation,[],[f122,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) | ~spl4_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f57])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    k5_relat_1(sK1,k6_relat_1(sK0)) = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) | (~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_7)),
% 0.20/0.48    inference(forward_demodulation,[],[f113,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) | ~spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f35])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    k5_relat_1(sK1,k6_relat_1(sK0)) = k5_relat_1(k5_relat_1(sK1,sK2),sK3) | (~spl4_2 | ~spl4_5 | ~spl4_6 | ~spl4_7)),
% 0.20/0.48    inference(resolution,[],[f66,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    v1_relat_1(sK1) | ~spl4_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f51])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X1,sK2),sK3) = k5_relat_1(X1,k6_relat_1(sK0))) ) | (~spl4_2 | ~spl4_5 | ~spl4_6)),
% 0.20/0.48    inference(forward_demodulation,[],[f64,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f31])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X1] : (k5_relat_1(k5_relat_1(X1,sK2),sK3) = k5_relat_1(X1,k5_relat_1(sK2,sK3)) | ~v1_relat_1(X1)) ) | (~spl4_5 | ~spl4_6)),
% 0.20/0.48    inference(resolution,[],[f60,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    v1_relat_1(sK2) | ~spl4_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f47])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),sK3) = k5_relat_1(X0,k5_relat_1(X1,sK3)) | ~v1_relat_1(X0)) ) | ~spl4_5),
% 0.20/0.48    inference(resolution,[],[f24,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    v1_relat_1(sK3) | ~spl4_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f43])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ~spl4_7 | spl4_8 | ~spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f54,f39,f57,f51])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    spl4_4 <=> r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    sK1 = k5_relat_1(sK1,k6_relat_1(sK0)) | ~v1_relat_1(sK1) | ~spl4_4),
% 0.20/0.48    inference(resolution,[],[f25,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(sK1),sK0) | ~spl4_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f39])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl4_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f16,f51])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    v1_relat_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ((sK1 != sK3 & k6_relat_1(sK0) = k5_relat_1(sK2,sK3) & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK3)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f14,f13,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (? [X3] : (X1 != X3 & k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (? [X3] : (sK1 != X3 & k5_relat_1(X2,X3) = k6_relat_1(sK0) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X2] : (? [X3] : (sK1 != X3 & k5_relat_1(X2,X3) = k6_relat_1(sK0) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,X2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) & v1_relat_1(X2)) => (? [X3] : (sK1 != X3 & k6_relat_1(sK0) = k5_relat_1(sK2,X3) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X3] : (sK1 != X3 & k6_relat_1(sK0) = k5_relat_1(sK2,X3) & k6_relat_1(k1_relat_1(X3)) = k5_relat_1(sK1,sK2) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(X3)) => (sK1 != sK3 & k6_relat_1(sK0) = k5_relat_1(sK2,sK3) & k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3)) & r1_tarski(k2_relat_1(sK1),sK0) & v1_relat_1(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (? [X3] : (X1 != X3 & k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f6])).
% 0.20/0.48  fof(f6,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : (? [X3] : ((X1 != X3 & (k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0))) & v1_relat_1(X3)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 0.20/0.48    inference(negated_conjecture,[],[f4])).
% 0.20/0.48  fof(f4,conjecture,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : (v1_relat_1(X3) => ((k6_relat_1(X0) = k5_relat_1(X2,X3) & k5_relat_1(X1,X2) = k6_relat_1(k1_relat_1(X3)) & r1_tarski(k2_relat_1(X1),X0)) => X1 = X3))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_relat_1)).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    spl4_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f17,f47])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl4_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f18,f43])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    v1_relat_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f19,f39])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f20,f35])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    k5_relat_1(sK1,sK2) = k6_relat_1(k1_relat_1(sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f31])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ~spl4_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f27])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    sK1 != sK3),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (24466)------------------------------
% 0.20/0.48  % (24466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24466)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (24466)Memory used [KB]: 10746
% 0.20/0.48  % (24466)Time elapsed: 0.038 s
% 0.20/0.48  % (24466)------------------------------
% 0.20/0.48  % (24466)------------------------------
% 0.20/0.48  % (24469)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (24459)Success in time 0.122 s
%------------------------------------------------------------------------------
