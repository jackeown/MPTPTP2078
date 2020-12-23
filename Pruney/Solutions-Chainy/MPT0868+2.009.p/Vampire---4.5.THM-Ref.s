%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 143 expanded)
%              Number of leaves         :   20 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  210 ( 352 expanded)
%              Number of equality atoms :   65 ( 130 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f43,f47,f55,f62,f69,f78,f84,f97,f105,f114,f122])).

fof(f122,plain,
    ( ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f119,f51])).

fof(f51,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_4
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f119,plain,
    ( sK2 != k2_mcart_1(sK2)
    | ~ spl3_12 ),
    inference(superposition,[],[f34,f104])).

fof(f104,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_12
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f34,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k2_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f114,plain,
    ( spl3_2
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl3_2
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f112,f42])).

fof(f42,plain,
    ( k1_xboole_0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f111,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f107,f33])).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f107,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k2_zfmisc_1(sK0,sK1) = X0 )
    | ~ spl3_7 ),
    inference(resolution,[],[f61,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f61,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl3_7
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f111,plain,
    ( sK1 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(resolution,[],[f107,f77])).

fof(f77,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f105,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f101,f57,f50,f103])).

fof(f57,plain,
    ( spl3_6
  <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f101,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f86,f51])).

fof(f86,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f85,f31])).

fof(f31,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f85,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_6 ),
    inference(resolution,[],[f58,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f58,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f97,plain,(
    ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f88,f90])).

fof(f90,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f25,f68])).

fof(f68,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_8
  <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f25,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f88,plain,
    ( sK2 != k1_mcart_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f35,f68])).

fof(f35,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | k1_mcart_1(X0) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,
    ( spl3_1
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f80,f38])).

fof(f38,plain,
    ( k1_xboole_0 != sK0
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_9 ),
    inference(resolution,[],[f79,f33])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK0 = X0 )
    | ~ spl3_9 ),
    inference(resolution,[],[f74,f32])).

fof(f74,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_9
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f78,plain,
    ( spl3_9
    | spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f70,f60,f76,f73])).

fof(f70,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f61,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

fof(f69,plain,
    ( spl3_8
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f65,f57,f53,f67])).

fof(f53,plain,
    ( spl3_5
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f65,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f64,f54])).

fof(f54,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f64,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f63,f31])).

fof(f63,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_6 ),
    inference(resolution,[],[f58,f24])).

fof(f62,plain,
    ( spl3_6
    | spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f48,f45,f60,f57])).

fof(f45,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f46,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f46,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f55,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f20,f53,f50])).

fof(f20,plain,
    ( sK2 = k1_mcart_1(sK2)
    | sK2 = k2_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => ( k2_mcart_1(X2) != X2
                  & k1_mcart_1(X2) != X2 ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f23,f41])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (14149)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (14163)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (14149)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f39,f43,f47,f55,f62,f69,f78,f84,f97,f105,f114,f122])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ~spl3_4 | ~spl3_12),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f121])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    $false | (~spl3_4 | ~spl3_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f119,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    sK2 = k2_mcart_1(sK2) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    spl3_4 <=> sK2 = k2_mcart_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    sK2 != k2_mcart_1(sK2) | ~spl3_12),
% 0.21/0.47    inference(superposition,[],[f34,f104])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | ~spl3_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl3_12 <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.47    inference(equality_resolution,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k2_mcart_1(X0) != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl3_2 | ~spl3_7 | ~spl3_10),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f113])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    $false | (spl3_2 | ~spl3_7 | ~spl3_10)),
% 0.21/0.47    inference(subsumption_resolution,[],[f112,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    k1_xboole_0 != sK1 | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl3_2 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | (~spl3_7 | ~spl3_10)),
% 0.21/0.47    inference(forward_demodulation,[],[f111,f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_7),
% 0.21/0.47    inference(resolution,[],[f107,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k2_zfmisc_1(sK0,sK1) = X0) ) | ~spl3_7),
% 0.21/0.47    inference(resolution,[],[f61,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl3_7 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    sK1 = k2_zfmisc_1(sK0,sK1) | (~spl3_7 | ~spl3_10)),
% 0.21/0.47    inference(resolution,[],[f107,f77])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    v1_xboole_0(sK1) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl3_10 <=> v1_xboole_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    spl3_12 | ~spl3_4 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f101,f57,f50,f103])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl3_6 <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | (~spl3_4 | ~spl3_6)),
% 0.21/0.47    inference(forward_demodulation,[],[f86,f51])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_6),
% 0.21/0.47    inference(subsumption_resolution,[],[f85,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_6),
% 0.21/0.47    inference(resolution,[],[f58,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ~spl3_8),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f96])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    $false | ~spl3_8),
% 0.21/0.47    inference(subsumption_resolution,[],[f88,f90])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    sK2 = k1_mcart_1(sK2) | ~spl3_8),
% 0.21/0.47    inference(superposition,[],[f25,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | ~spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl3_8 <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    sK2 != k1_mcart_1(sK2) | ~spl3_8),
% 0.21/0.47    inference(superposition,[],[f35,f68])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.47    inference(equality_resolution,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | k1_mcart_1(X0) != X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    spl3_1 | ~spl3_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    $false | (spl3_1 | ~spl3_9)),
% 0.21/0.47    inference(subsumption_resolution,[],[f80,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k1_xboole_0 != sK0 | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl3_1 <=> k1_xboole_0 = sK0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    k1_xboole_0 = sK0 | ~spl3_9),
% 0.21/0.47    inference(resolution,[],[f79,f33])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | sK0 = X0) ) | ~spl3_9),
% 0.21/0.47    inference(resolution,[],[f74,f32])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    v1_xboole_0(sK0) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl3_9 <=> v1_xboole_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl3_9 | spl3_10 | ~spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f70,f60,f76,f73])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    v1_xboole_0(sK1) | v1_xboole_0(sK0) | ~spl3_7),
% 0.21/0.47    inference(resolution,[],[f61,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl3_8 | ~spl3_5 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f65,f57,f53,f67])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl3_5 <=> sK2 = k1_mcart_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | (~spl3_5 | ~spl3_6)),
% 0.21/0.47    inference(forward_demodulation,[],[f64,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    sK2 = k1_mcart_1(sK2) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_6),
% 0.21/0.47    inference(subsumption_resolution,[],[f63,f31])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_6),
% 0.21/0.47    inference(resolution,[],[f58,f24])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl3_6 | spl3_7 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f48,f45,f60,f57])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl3_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f46,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f45])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl3_4 | spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f53,f50])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    sK2 = k1_mcart_1(sK2) | sK2 = k2_mcart_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f21,f45])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f41])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f37])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    k1_xboole_0 != sK0),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (14149)------------------------------
% 0.21/0.47  % (14149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14149)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (14149)Memory used [KB]: 6140
% 0.21/0.47  % (14149)Time elapsed: 0.056 s
% 0.21/0.47  % (14149)------------------------------
% 0.21/0.47  % (14149)------------------------------
% 0.21/0.47  % (14148)Success in time 0.109 s
%------------------------------------------------------------------------------
