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
% DateTime   : Thu Dec  3 12:59:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 165 expanded)
%              Number of leaves         :    5 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  179 (1223 expanded)
%              Number of equality atoms :  141 (1077 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f55,f97,f140])).

fof(f140,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl9_3 ),
    inference(unit_resulting_resolution,[],[f14,f13,f16,f15,f12,f43,f26])).

fof(f26,plain,(
    ! [X6,X4,X7,X5] :
      ( sK6 = k9_mcart_1(X4,X5,X6,X7,sK4)
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k1_xboole_0 = X4
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X4,X5,X6,X7)) ) ),
    inference(superposition,[],[f23,f11])).

fof(f11,plain,(
    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) != X8
            | k10_mcart_1(X0,X1,X2,X3,X4) != X7
            | k9_mcart_1(X0,X1,X2,X3,X4) != X6
            | k8_mcart_1(X0,X1,X2,X3,X4) != X5 )
          & k4_mcart_1(X5,X6,X7,X8) = X4 )
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
       => ~ ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & k1_xboole_0 != X3
            & k1_xboole_0 != X2
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f23,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X6 ) ),
    inference(equality_resolution,[],[f18])).

% (20747)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (20736)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (20723)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (20751)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (20743)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (20739)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (20739)Refutation not found, incomplete strategy% (20739)------------------------------
% (20739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f18,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) = X6 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5,X6,X7,X8] :
              ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              | k4_mcart_1(X5,X6,X7,X8) != X4 )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ? [X5,X6,X7,X8] :
                ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                    & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                    & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                    & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
                & k4_mcart_1(X5,X6,X7,X8) = X4 )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).

fof(f43,plain,
    ( sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl9_3
  <=> sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f12,plain,(
    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f8])).

fof(f14,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f97,plain,(
    spl9_2 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f14,f13,f16,f15,f12,f39,f27])).

fof(f27,plain,(
    ! [X10,X8,X11,X9] :
      ( sK7 = k10_mcart_1(X8,X9,X10,X11,sK4)
      | k1_xboole_0 = X9
      | k1_xboole_0 = X10
      | k1_xboole_0 = X11
      | k1_xboole_0 = X8
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X8,X9,X10,X11)) ) ),
    inference(superposition,[],[f22,f11])).

fof(f22,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7 ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k10_mcart_1(X0,X1,X2,X3,X4) = X7 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,
    ( sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl9_2
  <=> sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f55,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f14,f13,f16,f15,f12,f35,f28])).

fof(f28,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(sK4,k4_zfmisc_1(X12,X13,X14,X15))
      | k1_xboole_0 = X13
      | k1_xboole_0 = X14
      | k1_xboole_0 = X15
      | k1_xboole_0 = X12
      | sK8 = k11_mcart_1(X12,X13,X14,X15,sK4) ) ),
    inference(superposition,[],[f21,f11])).

fof(f21,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8 ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k11_mcart_1(X0,X1,X2,X3,X4) = X8 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,
    ( sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl9_1
  <=> sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f44,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f31,f41,f37,f33])).

fof(f31,plain,
    ( sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(trivial_inequality_removal,[],[f30])).

fof(f30,plain,
    ( sK5 != sK5
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(backward_demodulation,[],[f10,f29])).

fof(f29,plain,(
    sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f14,f13,f16,f15,f12,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( sK5 = k8_mcart_1(X0,X1,X2,X3,sK4)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | ~ m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(superposition,[],[f24,f11])).

fof(f24,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k1_xboole_0 = X0
      | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X5 ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f9])).

% (20729)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f10,plain,
    ( sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4)
    | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:37:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.56  % (20726)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (20744)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (20725)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (20726)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (20748)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (20730)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.57  % (20740)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f44,f55,f97,f140])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    spl9_3),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f137])).
% 0.21/0.57  fof(f137,plain,(
% 0.21/0.57    $false | spl9_3),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f14,f13,f16,f15,f12,f43,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ( ! [X6,X4,X7,X5] : (sK6 = k9_mcart_1(X4,X5,X6,X7,sK4) | k1_xboole_0 = X5 | k1_xboole_0 = X6 | k1_xboole_0 = X7 | k1_xboole_0 = X4 | ~m1_subset_1(sK4,k4_zfmisc_1(X4,X5,X6,X7))) )),
% 0.21/0.57    inference(superposition,[],[f23,f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    sK4 = k4_mcart_1(sK5,sK6,sK7,sK8)),
% 0.21/0.57    inference(cnf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3,X4] : (? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.57    inference(flattening,[],[f7])).
% 0.21/0.57  fof(f7,plain,(
% 0.21/0.57    ? [X0,X1,X2,X3,X4] : ((? [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) != X8 | k10_mcart_1(X0,X1,X2,X3,X4) != X7 | k9_mcart_1(X0,X1,X2,X3,X4) != X6 | k8_mcart_1(X0,X1,X2,X3,X4) != X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.57    inference(negated_conjecture,[],[f5])).
% 0.21/0.57  fof(f5,conjecture,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X6) )),
% 0.21/0.57    inference(equality_resolution,[],[f18])).
% 0.21/0.57  % (20747)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (20736)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (20723)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (20751)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.57  % (20743)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.57  % (20739)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (20739)Refutation not found, incomplete strategy% (20739)------------------------------
% 0.21/0.57  % (20739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) = X6) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,plain,(
% 0.21/0.58    ! [X0,X1,X2,X3] : (! [X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.58    inference(ennf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1,X2,X3] : ~(? [X4] : (? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_mcart_1)).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | spl9_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    spl9_3 <=> sK6 = k9_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.58  fof(f12,plain,(
% 0.21/0.58    m1_subset_1(sK4,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    k1_xboole_0 != sK2),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    k1_xboole_0 != sK3),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    k1_xboole_0 != sK0),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    k1_xboole_0 != sK1),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  fof(f97,plain,(
% 0.21/0.58    spl9_2),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.58  fof(f94,plain,(
% 0.21/0.58    $false | spl9_2),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f14,f13,f16,f15,f12,f39,f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ( ! [X10,X8,X11,X9] : (sK7 = k10_mcart_1(X8,X9,X10,X11,sK4) | k1_xboole_0 = X9 | k1_xboole_0 = X10 | k1_xboole_0 = X11 | k1_xboole_0 = X8 | ~m1_subset_1(sK4,k4_zfmisc_1(X8,X9,X10,X11))) )),
% 0.21/0.58    inference(superposition,[],[f22,f11])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k10_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X7) )),
% 0.21/0.58    inference(equality_resolution,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k10_mcart_1(X0,X1,X2,X3,X4) = X7) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | spl9_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    spl9_2 <=> sK7 = k10_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    spl9_1),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    $false | spl9_1),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f14,f13,f16,f15,f12,f35,f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ( ! [X14,X12,X15,X13] : (~m1_subset_1(sK4,k4_zfmisc_1(X12,X13,X14,X15)) | k1_xboole_0 = X13 | k1_xboole_0 = X14 | k1_xboole_0 = X15 | k1_xboole_0 = X12 | sK8 = k11_mcart_1(X12,X13,X14,X15,sK4)) )),
% 0.21/0.58    inference(superposition,[],[f21,f11])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k11_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X8) )),
% 0.21/0.58    inference(equality_resolution,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k11_mcart_1(X0,X1,X2,X3,X4) = X8) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4) | spl9_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    spl9_1 <=> sK8 = k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f31,f41,f37,f33])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    sK5 != sK5 | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.58    inference(backward_demodulation,[],[f10,f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    sK5 = k8_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.58    inference(unit_resulting_resolution,[],[f14,f13,f16,f15,f12,f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (sK5 = k8_mcart_1(X0,X1,X2,X3,sK4) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | ~m1_subset_1(sK4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.21/0.58    inference(superposition,[],[f24,f11])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(k4_mcart_1(X5,X6,X7,X8),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k1_xboole_0 = X0 | k8_mcart_1(X0,X1,X2,X3,k4_mcart_1(X5,X6,X7,X8)) = X5) )),
% 0.21/0.58    inference(equality_resolution,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(X5,X6,X7,X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 0.21/0.58    inference(cnf_transformation,[],[f9])).
% 0.21/0.58  % (20729)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.58  fof(f10,plain,(
% 0.21/0.58    sK5 != k8_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK6 != k9_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK7 != k10_mcart_1(sK0,sK1,sK2,sK3,sK4) | sK8 != k11_mcart_1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.58    inference(cnf_transformation,[],[f8])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (20726)------------------------------
% 0.21/0.58  % (20726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (20726)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (20726)Memory used [KB]: 6268
% 0.21/0.58  % (20726)Time elapsed: 0.136 s
% 0.21/0.58  % (20726)------------------------------
% 0.21/0.58  % (20726)------------------------------
% 0.21/0.58  % (20739)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (20719)Success in time 0.219 s
%------------------------------------------------------------------------------
