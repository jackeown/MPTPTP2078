%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 152 expanded)
%              Number of leaves         :    4 (  34 expanded)
%              Depth                    :   24
%              Number of atoms          :  237 ( 907 expanded)
%              Number of equality atoms :  236 ( 906 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(subsumption_resolution,[],[f163,f14])).

fof(f14,plain,(
    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( sK3 != sK7
      | sK2 != sK6
      | sK1 != sK5
      | sK0 != sK4 )
    & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
    & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f9])).

% (27393)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( ( X3 != X7
          | X2 != X6
          | X1 != X5
          | X0 != X4 )
        & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) )
   => ( ( sK3 != sK7
        | sK2 != sK6
        | sK1 != sK5
        | sK0 != sK4 )
      & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 != X7
        | X2 != X6
        | X1 != X5
        | X0 != X4 )
      & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] :
        ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
       => ( ( X3 = X7
            & X2 = X6
            & X1 = X5
            & X0 = X4 )
          | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).

fof(f163,plain,(
    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) ),
    inference(forward_demodulation,[],[f157,f28])).

fof(f28,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k4_zfmisc_1(k1_xboole_0,X1,X2,X3) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f157,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(k1_xboole_0,sK5,sK6,sK7) ),
    inference(backward_demodulation,[],[f13,f156])).

fof(f156,plain,(
    k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f155,f14])).

fof(f155,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f151,f27])).

fof(f27,plain,(
    ! [X2,X0,X3] : k1_xboole_0 = k4_zfmisc_1(X0,k1_xboole_0,X2,X3) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f151,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,k1_xboole_0,sK6,sK7)
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f13,f146])).

fof(f146,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f145,f14])).

fof(f145,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f141,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,k1_xboole_0,X3) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f141,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,k1_xboole_0,sK7)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f13,f122])).

fof(f122,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f121,f14])).

fof(f121,plain,
    ( k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(forward_demodulation,[],[f117,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,k1_xboole_0) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f117,plain,
    ( k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,k1_xboole_0)
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f13,f105])).

fof(f105,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f104,f43])).

fof(f43,plain,
    ( sK0 = sK4
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)
      | sK4 = X0
      | k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f21,f13])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X0 = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)
     => ( ( X3 = X7
          & X2 = X6
          & X1 = X5
          & X0 = X4 )
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).

fof(f104,plain,
    ( sK0 != sK4
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f103,f58])).

fof(f58,plain,
    ( sK1 = sK5
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X10,X8,X11,X9] :
      ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X8,X9,X10,X11)
      | sK5 = X9
      | k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f22,f13])).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X1 = X5
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f103,plain,
    ( sK1 != sK5
    | sK0 != sK4
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(subsumption_resolution,[],[f102,f71])).

fof(f71,plain,
    ( sK2 = sK6
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X19,X17,X18,X16] :
      ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X16,X17,X18,X19)
      | sK6 = X18
      | k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f23,f13])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X2 = X6
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f102,plain,
    ( sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( sK3 != sK3
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f15,f85])).

fof(f85,plain,
    ( sK3 = sK7
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK6
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4 ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X26,X24,X27,X25] :
      ( k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X24,X25,X26,X27)
      | sK7 = X27
      | k1_xboole_0 = sK7
      | k1_xboole_0 = sK6
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f24,f13])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( X3 = X7
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,
    ( sK3 != sK7
    | sK2 != sK6
    | sK1 != sK5
    | sK0 != sK4 ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:13:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (27378)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.49  % (27378)Refutation not found, incomplete strategy% (27378)------------------------------
% 0.22/0.49  % (27378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (27378)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (27378)Memory used [KB]: 10618
% 0.22/0.50  % (27378)Time elapsed: 0.069 s
% 0.22/0.50  % (27378)------------------------------
% 0.22/0.50  % (27378)------------------------------
% 0.22/0.51  % (27386)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (27385)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (27377)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (27390)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (27394)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.53  % (27390)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f163,f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    (sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f6,f9])).
% 0.22/0.53  % (27393)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7)) => ((sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4) & k1_xboole_0 != k4_zfmisc_1(sK0,sK1,sK2,sK3) & k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f6,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.22/0.53    inference(flattening,[],[f5])).
% 0.22/0.53  fof(f5,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 != X7 | X2 != X6 | X1 != X5 | X0 != X4) & k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)) & k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.53    inference(negated_conjecture,[],[f3])).
% 0.22/0.53  fof(f3,conjecture,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_mcart_1)).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 0.22/0.53    inference(forward_demodulation,[],[f157,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X2,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(k1_xboole_0,X1,X2,X3)) )),
% 0.22/0.53    inference(equality_resolution,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(k1_xboole_0,sK5,sK6,sK7)),
% 0.22/0.53    inference(backward_demodulation,[],[f13,f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f155,f14])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK4),
% 0.22/0.53    inference(forward_demodulation,[],[f151,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X2,X0,X3] : (k1_xboole_0 = k4_zfmisc_1(X0,k1_xboole_0,X2,X3)) )),
% 0.22/0.53    inference(equality_resolution,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,k1_xboole_0,sK6,sK7) | k1_xboole_0 = sK4),
% 0.22/0.53    inference(superposition,[],[f13,f146])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f145,f14])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(forward_demodulation,[],[f141,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,k1_xboole_0,X3)) )),
% 0.22/0.53    inference(equality_resolution,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,k1_xboole_0,sK7) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(superposition,[],[f13,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f121,f14])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    k1_xboole_0 = k4_zfmisc_1(sK0,sK1,sK2,sK3) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(forward_demodulation,[],[f117,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,k1_xboole_0) | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(superposition,[],[f13,f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f104,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    sK0 = sK4 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(equality_resolution,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(sK0,sK1,sK2,sK3) | sK4 = X0 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4) )),
% 0.22/0.53    inference(superposition,[],[f21,f13])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X0 = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 0.22/0.53    inference(flattening,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_zfmisc_1(X0,X1,X2,X3) = k4_zfmisc_1(X4,X5,X6,X7) => ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_mcart_1)).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    sK0 != sK4 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f103,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    sK1 = sK5 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(equality_resolution,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X10,X8,X11,X9] : (k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X8,X9,X10,X11) | sK5 = X9 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4) )),
% 0.22/0.53    inference(superposition,[],[f22,f13])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X1 = X5 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    sK1 != sK5 | sK0 != sK4 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(subsumption_resolution,[],[f102,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    sK2 = sK6 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(equality_resolution,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X19,X17,X18,X16] : (k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X16,X17,X18,X19) | sK6 = X18 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4) )),
% 0.22/0.53    inference(superposition,[],[f23,f13])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X2 = X6 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    sK2 != sK6 | sK1 != sK5 | sK0 != sK4 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    sK3 != sK3 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(superposition,[],[f15,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    sK3 = sK7 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4),
% 0.22/0.53    inference(equality_resolution,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X26,X24,X27,X25] : (k4_zfmisc_1(sK0,sK1,sK2,sK3) != k4_zfmisc_1(X24,X25,X26,X27) | sK7 = X27 | k1_xboole_0 = sK7 | k1_xboole_0 = sK6 | k1_xboole_0 = sK5 | k1_xboole_0 = sK4) )),
% 0.22/0.53    inference(superposition,[],[f24,f13])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (X3 = X7 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k4_zfmisc_1(X0,X1,X2,X3) != k4_zfmisc_1(X4,X5,X6,X7)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    sK3 != sK7 | sK2 != sK6 | sK1 != sK5 | sK0 != sK4),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    k4_zfmisc_1(sK0,sK1,sK2,sK3) = k4_zfmisc_1(sK4,sK5,sK6,sK7)),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (27390)------------------------------
% 0.22/0.53  % (27390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (27390)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (27390)Memory used [KB]: 1663
% 0.22/0.53  % (27390)Time elapsed: 0.104 s
% 0.22/0.53  % (27390)------------------------------
% 0.22/0.53  % (27390)------------------------------
% 0.22/0.53  % (27370)Success in time 0.165 s
%------------------------------------------------------------------------------
