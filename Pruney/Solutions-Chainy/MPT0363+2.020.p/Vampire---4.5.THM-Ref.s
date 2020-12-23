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
% DateTime   : Thu Dec  3 12:45:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 126 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :  222 ( 444 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f48,f53,f58,f77,f108,f115,f119,f232,f254])).

% (16817)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f254,plain,
    ( ~ spl4_5
    | spl4_8
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl4_5
    | spl4_8
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f244,f114])).

fof(f114,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_8
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f244,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(resolution,[],[f141,f231])).

fof(f231,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl4_18
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f141,plain,
    ( ! [X3] :
        ( ~ r1_tarski(sK1,X3)
        | r1_tarski(sK1,k4_xboole_0(X3,sK2)) )
    | ~ spl4_5 ),
    inference(superposition,[],[f36,f65])).

fof(f65,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl4_5
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f232,plain,
    ( spl4_18
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f227,f55,f229])).

fof(f55,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f227,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f105,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f105,plain,
    ( ! [X4] :
        ( r2_hidden(sK3(sK1,X4),sK0)
        | r1_tarski(sK1,X4) )
    | ~ spl4_4 ),
    inference(resolution,[],[f79,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f57,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f57,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f119,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f117,f40,f64])).

fof(f40,plain,
    ( spl4_1
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f117,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f41,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f41,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f115,plain,
    ( ~ spl4_8
    | spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f110,f73,f44,f112])).

fof(f44,plain,
    ( spl4_2
  <=> r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f73,plain,
    ( spl4_6
  <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f110,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f46,f75])).

fof(f75,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f46,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f108,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f106,f59])).

fof(f59,plain,
    ( ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(X0,sK2))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f42,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f42,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f106,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f45,f75])).

fof(f45,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f77,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f71,f50,f73])).

fof(f50,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f71,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f52,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

% (16796)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f58,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

% (16798)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f19,plain,
    ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | ~ r1_xboole_0(sK1,sK2) )
    & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
      | r1_xboole_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
            | ~ r1_xboole_0(sK1,X2) )
          & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
            | r1_xboole_0(sK1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,X2))
          | ~ r1_xboole_0(sK1,X2) )
        & ( r1_tarski(sK1,k3_subset_1(sK0,X2))
          | r1_xboole_0(sK1,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | ~ r1_xboole_0(sK1,sK2) )
      & ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
        | r1_xboole_0(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f53,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f27,f44,f40])).

fof(f27,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f47,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f28,f44,f40])).

fof(f28,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK2))
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 13:29:15 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.49  % (16801)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (16792)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (16795)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (16818)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.50  % (16807)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (16799)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (16803)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (16818)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f255,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f47,f48,f53,f58,f77,f108,f115,f119,f232,f254])).
% 0.20/0.51  % (16817)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  fof(f254,plain,(
% 0.20/0.51    ~spl4_5 | spl4_8 | ~spl4_18),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f253])).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    $false | (~spl4_5 | spl4_8 | ~spl4_18)),
% 0.20/0.51    inference(subsumption_resolution,[],[f244,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | spl4_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f112])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    spl4_8 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f244,plain,(
% 0.20/0.51    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (~spl4_5 | ~spl4_18)),
% 0.20/0.51    inference(resolution,[],[f141,f231])).
% 0.20/0.51  fof(f231,plain,(
% 0.20/0.51    r1_tarski(sK1,sK0) | ~spl4_18),
% 0.20/0.51    inference(avatar_component_clause,[],[f229])).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    spl4_18 <=> r1_tarski(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    ( ! [X3] : (~r1_tarski(sK1,X3) | r1_tarski(sK1,k4_xboole_0(X3,sK2))) ) | ~spl4_5),
% 0.20/0.51    inference(superposition,[],[f36,f65])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    sK1 = k4_xboole_0(sK1,sK2) | ~spl4_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    spl4_5 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    spl4_18 | ~spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f227,f55,f229])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    r1_tarski(sK1,sK0) | ~spl4_4),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f224])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f105,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ( ! [X4] : (r2_hidden(sK3(sK1,X4),sK0) | r1_tarski(sK1,X4)) ) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f79,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl4_4),
% 0.20/0.51    inference(resolution,[],[f57,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f55])).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    spl4_5 | ~spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f117,f40,f64])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    spl4_1 <=> r1_xboole_0(sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    sK1 = k4_xboole_0(sK1,sK2) | ~spl4_1),
% 0.20/0.51    inference(resolution,[],[f41,f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    r1_xboole_0(sK1,sK2) | ~spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f40])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ~spl4_8 | spl4_2 | ~spl4_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f110,f73,f44,f112])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    spl4_2 <=> r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    spl4_6 <=> k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ~r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (spl4_2 | ~spl4_6)),
% 0.20/0.51    inference(forward_demodulation,[],[f46,f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f73])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f44])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl4_1 | ~spl4_2 | ~spl4_6),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    $false | (spl4_1 | ~spl4_2 | ~spl4_6)),
% 0.20/0.51    inference(subsumption_resolution,[],[f106,f59])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(X0,sK2))) ) | spl4_1),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f42,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ~r1_xboole_0(sK1,sK2) | spl4_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f40])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    r1_tarski(sK1,k4_xboole_0(sK0,sK2)) | (~spl4_2 | ~spl4_6)),
% 0.20/0.51    inference(backward_demodulation,[],[f45,f75])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f44])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl4_6 | ~spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f71,f50,f73])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | ~spl4_3),
% 0.20/0.51    inference(resolution,[],[f52,f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.51  % (16796)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f50])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f55])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  % (16798)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X2] : ((~r1_tarski(sK1,k3_subset_1(sK0,X2)) | ~r1_xboole_0(sK1,X2)) & (r1_tarski(sK1,k3_subset_1(sK0,X2)) | r1_xboole_0(sK1,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)) & (r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2)) & (r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,X2) <~> r1_tarski(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f7])).
% 0.20/0.51  fof(f7,conjecture,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f26,f50])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    spl4_1 | spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f27,f44,f40])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    r1_tarski(sK1,k3_subset_1(sK0,sK2)) | r1_xboole_0(sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f44,f40])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ~r1_tarski(sK1,k3_subset_1(sK0,sK2)) | ~r1_xboole_0(sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (16818)------------------------------
% 0.20/0.51  % (16818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16818)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (16818)Memory used [KB]: 6268
% 0.20/0.51  % (16818)Time elapsed: 0.063 s
% 0.20/0.51  % (16818)------------------------------
% 0.20/0.51  % (16818)------------------------------
% 0.20/0.51  % (16793)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (16788)Success in time 0.154 s
%------------------------------------------------------------------------------
