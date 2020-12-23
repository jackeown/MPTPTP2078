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
% DateTime   : Thu Dec  3 12:58:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 123 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :  191 ( 365 expanded)
%              Number of equality atoms :   65 ( 172 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f64,f95,f104,f108,f116,f121,f125,f140,f148])).

fof(f148,plain,
    ( ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f40,f141])).

fof(f141,plain,
    ( sK2 != k1_mcart_1(sK2)
    | ~ spl3_10 ),
    inference(superposition,[],[f36,f130])).

fof(f130,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_10
  <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f36,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f40,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl3_1
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f140,plain,
    ( ~ spl3_9
    | spl3_10
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f139,f61,f38,f128,f85])).

fof(f85,plain,
    ( spl3_9
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f61,plain,
    ( spl3_6
  <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f139,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f138,f40])).

fof(f138,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(resolution,[],[f63,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f63,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f125,plain,(
    ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f23,f74,f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f74,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ( k2_mcart_1(X2) = X2
          | k1_mcart_1(X2) = X2 )
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => ( k2_mcart_1(X2) != X2
                  & k1_mcart_1(X2) != X2 ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f121,plain,
    ( spl3_7
    | spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f119,f57,f72,f68])).

fof(f68,plain,
    ( spl3_7
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f57,plain,
    ( spl3_5
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f59,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

fof(f59,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f116,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f44,f110])).

fof(f110,plain,
    ( sK2 != k2_mcart_1(sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f35,f53])).

fof(f53,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl3_4
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f35,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_2
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f108,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f34,f87])).

fof(f87,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f104,plain,
    ( ~ spl3_9
    | spl3_4
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f103,f61,f42,f51,f85])).

fof(f103,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f102,f44])).

fof(f102,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl3_6 ),
    inference(resolution,[],[f63,f29])).

fof(f95,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f22,f70,f28])).

fof(f70,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f55,f61,f57])).

fof(f55,plain,
    ( r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f24,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f24,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f25,f42,f38])).

fof(f25,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:44:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (18748)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (18740)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (18751)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  % (18743)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (18751)Refutation not found, incomplete strategy% (18751)------------------------------
% 0.20/0.47  % (18751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18743)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (18751)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (18751)Memory used [KB]: 1663
% 0.20/0.48  % (18751)Time elapsed: 0.074 s
% 0.20/0.48  % (18751)------------------------------
% 0.20/0.48  % (18751)------------------------------
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f149,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f45,f64,f95,f104,f108,f116,f121,f125,f140,f148])).
% 0.20/0.48  fof(f148,plain,(
% 0.20/0.48    ~spl3_1 | ~spl3_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f144])).
% 0.20/0.48  fof(f144,plain,(
% 0.20/0.48    $false | (~spl3_1 | ~spl3_10)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f40,f141])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    sK2 != k1_mcart_1(sK2) | ~spl3_10),
% 0.20/0.48    inference(superposition,[],[f36,f130])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | ~spl3_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f128])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    spl3_10 <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.20/0.48    inference(equality_resolution,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    sK2 = k1_mcart_1(sK2) | ~spl3_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    spl3_1 <=> sK2 = k1_mcart_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ~spl3_9 | spl3_10 | ~spl3_1 | ~spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f139,f61,f38,f128,f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl3_9 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl3_6 <=> r2_hidden(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl3_1 | ~spl3_6)),
% 0.20/0.48    inference(forward_demodulation,[],[f138,f40])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl3_6),
% 0.20/0.48    inference(resolution,[],[f63,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f61])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ~spl3_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    $false | ~spl3_8),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f23,f74,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | ~spl3_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl3_8 <=> v1_xboole_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    k1_xboole_0 != sK1),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    spl3_7 | spl3_8 | ~spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f119,f57,f72,f68])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl3_7 <=> v1_xboole_0(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl3_5 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | v1_xboole_0(sK0) | ~spl3_5),
% 0.20/0.48    inference(resolution,[],[f59,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | ~spl3_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f57])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ~spl3_2 | ~spl3_4),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f112])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    $false | (~spl3_2 | ~spl3_4)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f44,f110])).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    sK2 != k2_mcart_1(sK2) | ~spl3_4),
% 0.20/0.48    inference(superposition,[],[f35,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | ~spl3_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl3_4 <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.20/0.48    inference(equality_resolution,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    sK2 = k2_mcart_1(sK2) | ~spl3_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    spl3_2 <=> sK2 = k2_mcart_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    spl3_9),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f105])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    $false | spl3_9),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f34,f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f85])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ~spl3_9 | spl3_4 | ~spl3_2 | ~spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f103,f61,f42,f51,f85])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl3_2 | ~spl3_6)),
% 0.20/0.48    inference(forward_demodulation,[],[f102,f44])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl3_6),
% 0.20/0.48    inference(resolution,[],[f63,f29])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ~spl3_7),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f93])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    $false | ~spl3_7),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f22,f70,f28])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    v1_xboole_0(sK0) | ~spl3_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f68])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    spl3_5 | spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f55,f61,f57])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    r2_hidden(sK2,k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 0.20/0.48    inference(resolution,[],[f24,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl3_1 | spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f25,f42,f38])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (18743)------------------------------
% 0.20/0.48  % (18743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (18743)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (18743)Memory used [KB]: 6140
% 0.20/0.48  % (18743)Time elapsed: 0.078 s
% 0.20/0.48  % (18743)------------------------------
% 0.20/0.48  % (18743)------------------------------
% 0.20/0.48  % (18737)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (18732)Success in time 0.131 s
%------------------------------------------------------------------------------
