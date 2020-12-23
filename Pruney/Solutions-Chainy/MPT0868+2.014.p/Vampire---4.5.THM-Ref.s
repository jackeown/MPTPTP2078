%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 135 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  206 ( 404 expanded)
%              Number of equality atoms :  104 ( 221 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f83,f85,f96,f103,f112,f117,f124])).

fof(f124,plain,(
    ~ spl3_12 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl3_12 ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,
    ( sK2 != sK2
    | ~ spl3_12 ),
    inference(superposition,[],[f67,f115])).

fof(f115,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_12
  <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f67,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X0 ),
    inference(superposition,[],[f38,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f38,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f117,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f116,f110,f42,f114])).

fof(f42,plain,
    ( spl3_1
  <=> sK2 = k1_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f110,plain,
    ( spl3_11
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f116,plain,
    ( sK2 = k4_tarski(sK2,k2_mcart_1(sK2))
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f111,f43])).

fof(f43,plain,
    ( sK2 = k1_mcart_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f111,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( spl3_7
    | ~ spl3_8
    | spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f72,f49,f110,f78,f75])).

fof(f75,plain,
    ( spl3_7
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f78,plain,
    ( spl3_8
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f49,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f72,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f71,f50])).

fof(f50,plain,
    ( m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f70,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_relat_1(X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f103,plain,(
    ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f99])).

fof(f99,plain,
    ( sK2 != sK2
    | ~ spl3_9 ),
    inference(superposition,[],[f66,f82])).

fof(f82,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_9
  <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f66,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X1 ),
    inference(superposition,[],[f37,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f96,plain,
    ( spl3_4
    | spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f89,f75,f57,f53])).

fof(f53,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f89,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f87])).

fof(f87,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | ~ spl3_7 ),
    inference(superposition,[],[f34,f76])).

fof(f76,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f75])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f85,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl3_8 ),
    inference(resolution,[],[f79,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f79,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f83,plain,
    ( spl3_7
    | ~ spl3_8
    | spl3_9
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f73,f49,f45,f81,f78,f75])).

fof(f45,plain,
    ( spl3_2
  <=> sK2 = k2_mcart_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( sK2 = k4_tarski(k1_mcart_1(sK2),sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f72,f46])).

fof(f46,plain,
    ( sK2 = k2_mcart_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f59,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f22,f57])).

fof(f22,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17])).

fof(f17,plain,
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

fof(f18,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f55,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f25,f45,f42])).

fof(f25,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (26770)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.42  % (26770)Refutation not found, incomplete strategy% (26770)------------------------------
% 0.21/0.42  % (26770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (26770)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (26770)Memory used [KB]: 1535
% 0.21/0.42  % (26770)Time elapsed: 0.002 s
% 0.21/0.42  % (26770)------------------------------
% 0.21/0.42  % (26770)------------------------------
% 0.21/0.45  % (26763)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.45  % (26763)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f126,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f83,f85,f96,f103,f112,f117,f124])).
% 0.21/0.45  fof(f124,plain,(
% 0.21/0.45    ~spl3_12),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    $false | ~spl3_12),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f118])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    sK2 != sK2 | ~spl3_12),
% 0.21/0.45    inference(superposition,[],[f67,f115])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | ~spl3_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f114])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    spl3_12 <=> sK2 = k4_tarski(sK2,k2_mcart_1(sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_tarski(X0,X1) != X0) )),
% 0.21/0.45    inference(superposition,[],[f38,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.45    inference(equality_resolution,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    spl3_12 | ~spl3_1 | ~spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f116,f110,f42,f114])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    spl3_1 <=> sK2 = k1_mcart_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f110,plain,(
% 0.21/0.45    spl3_11 <=> sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    sK2 = k4_tarski(sK2,k2_mcart_1(sK2)) | (~spl3_1 | ~spl3_11)),
% 0.21/0.45    inference(forward_demodulation,[],[f111,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    sK2 = k1_mcart_1(sK2) | ~spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f42])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~spl3_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f110])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    spl3_7 | ~spl3_8 | spl3_11 | ~spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f72,f49,f110,f78,f75])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    spl3_7 <=> k1_xboole_0 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl3_8 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    spl3_3 <=> m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    sK2 = k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_3),
% 0.21/0.45    inference(resolution,[],[f71,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f49])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k4_tarski(k1_mcart_1(X1),k2_mcart_1(X1)) = X1 | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(resolution,[],[f70,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_relat_1(X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~m1_subset_1(X0,X1)) )),
% 0.21/0.45    inference(resolution,[],[f32,f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    ~spl3_9),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f102])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    $false | ~spl3_9),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f99])).
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    sK2 != sK2 | ~spl3_9),
% 0.21/0.45    inference(superposition,[],[f66,f82])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | ~spl3_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f81])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    spl3_9 <=> sK2 = k4_tarski(k1_mcart_1(sK2),sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_tarski(X0,X1) != X1) )),
% 0.21/0.45    inference(superposition,[],[f37,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.45    inference(equality_resolution,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    spl3_4 | spl3_5 | ~spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f89,f75,f57,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl3_4 <=> k1_xboole_0 = sK1),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    spl3_5 <=> k1_xboole_0 = sK0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl3_7),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f87])).
% 0.21/0.45  fof(f87,plain,(
% 0.21/0.45    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | ~spl3_7),
% 0.21/0.45    inference(superposition,[],[f34,f76])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f75])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.45    inference(cnf_transformation,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.45    inference(flattening,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl3_8),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    $false | spl3_8),
% 0.21/0.45    inference(resolution,[],[f79,f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f78])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    spl3_7 | ~spl3_8 | spl3_9 | ~spl3_2 | ~spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f73,f49,f45,f81,f78,f75])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    spl3_2 <=> sK2 = k2_mcart_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    sK2 = k4_tarski(k1_mcart_1(sK2),sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | (~spl3_2 | ~spl3_3)),
% 0.21/0.45    inference(forward_demodulation,[],[f72,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    sK2 = k2_mcart_1(sK2) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f45])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ~spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f22,f57])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    k1_xboole_0 != sK0),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f18,f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.45    inference(negated_conjecture,[],[f8])).
% 0.21/0.45  fof(f8,conjecture,(
% 0.21/0.45    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ~spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f53])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    k1_xboole_0 != sK1),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f49])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl3_1 | spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f45,f42])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f19])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (26763)------------------------------
% 0.21/0.45  % (26763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (26763)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (26763)Memory used [KB]: 10618
% 0.21/0.46  % (26763)Time elapsed: 0.007 s
% 0.21/0.46  % (26763)------------------------------
% 0.21/0.46  % (26763)------------------------------
% 0.21/0.46  % (26756)Success in time 0.102 s
%------------------------------------------------------------------------------
