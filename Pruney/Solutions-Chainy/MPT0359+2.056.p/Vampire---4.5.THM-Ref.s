%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 212 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  228 ( 602 expanded)
%              Number of equality atoms :   44 ( 189 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f321,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f76,f114,f153,f190,f201,f238,f320])).

fof(f320,plain,
    ( ~ spl3_2
    | spl3_3
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | ~ spl3_2
    | spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f318,f274])).

fof(f274,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl3_2
    | spl3_3 ),
    inference(backward_demodulation,[],[f74,f68])).

fof(f68,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f74,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_3
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

% (26072)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f318,plain,
    ( r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl3_4 ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,
    ( r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f309,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

% (26068)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f309,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k3_subset_1(sK0,sK0),X0),sK0)
        | r1_tarski(k3_subset_1(sK0,sK0),X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f130,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f130,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_subset_1(sK0,sK0))
        | r2_hidden(X1,sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f88,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f88,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_4
  <=> m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f238,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f213,f220])).

fof(f220,plain,
    ( ~ r1_tarski(k1_subset_1(sK0),sK0)
    | spl3_1
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f65,f209])).

fof(f209,plain,
    ( k1_subset_1(sK0) = k3_subset_1(sK0,sK0)
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f152,f199])).

fof(f199,plain,
    ( sK0 = sK1
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f193,f55])).

fof(f55,plain,(
    ! [X0] : k3_subset_1(X0,k1_subset_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f193,plain,
    ( sK1 = k3_subset_1(sK0,k1_subset_1(sK0))
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f117,f152])).

fof(f117,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f152,plain,
    ( k3_subset_1(sK0,sK1) = k1_subset_1(sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_14
  <=> k3_subset_1(sK0,sK1) = k1_subset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f65,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_1
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f213,plain,
    ( r1_tarski(k1_subset_1(sK0),sK0)
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f191,f199])).

fof(f191,plain,
    ( r1_tarski(k1_subset_1(sK0),sK1)
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f75,f152])).

fof(f75,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f201,plain,
    ( spl3_2
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl3_2
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f199,f69])).

fof(f69,plain,
    ( sK0 != sK1
    | spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f190,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl3_11 ),
    inference(subsumption_resolution,[],[f188,f33])).

fof(f188,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_11 ),
    inference(resolution,[],[f139,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f139,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl3_11
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f153,plain,
    ( ~ spl3_11
    | spl3_14
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f148,f73,f150,f137])).

fof(f148,plain,
    ( k3_subset_1(sK0,sK1) = k1_subset_1(sK0)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f134,f75])).

fof(f134,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) = k1_subset_1(sK0)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f42,f117])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k1_subset_1(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(X1,k3_subset_1(X0,X1))
          | k1_subset_1(X0) != X1 )
        & ( k1_subset_1(X0) = X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f114,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f112,f78])).

fof(f78,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f33,f68])).

fof(f112,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_4 ),
    inference(resolution,[],[f89,f40])).

fof(f89,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f76,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f71,f67,f73])).

fof(f71,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f54,f55])).

fof(f54,plain,
    ( sK1 = k3_subset_1(sK0,k1_subset_1(sK0))
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f34,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f70,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f61,f67,f63])).

fof(f61,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    inference(inner_rewriting,[],[f60])).

fof(f60,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f53,f55])).

fof(f53,plain,
    ( sK1 != k3_subset_1(sK0,k1_subset_1(sK0))
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f35,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (26057)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.48  % (26063)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (26043)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (26045)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (26046)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (26051)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (26046)Refutation not found, incomplete strategy% (26046)------------------------------
% 0.22/0.54  % (26046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (26046)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (26046)Memory used [KB]: 6268
% 0.22/0.54  % (26046)Time elapsed: 0.124 s
% 0.22/0.54  % (26046)------------------------------
% 0.22/0.54  % (26046)------------------------------
% 0.22/0.54  % (26044)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (26042)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (26071)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (26069)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (26062)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (26055)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (26061)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (26047)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.56  % (26066)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (26050)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (26056)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (26052)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (26064)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (26067)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (26058)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (26059)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (26048)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (26070)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (26060)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (26065)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (26060)Refutation not found, incomplete strategy% (26060)------------------------------
% 0.22/0.57  % (26060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (26060)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (26060)Memory used [KB]: 10618
% 0.22/0.57  % (26060)Time elapsed: 0.155 s
% 0.22/0.57  % (26060)------------------------------
% 0.22/0.57  % (26060)------------------------------
% 0.22/0.57  % (26050)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f321,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f70,f76,f114,f153,f190,f201,f238,f320])).
% 0.22/0.57  fof(f320,plain,(
% 0.22/0.57    ~spl3_2 | spl3_3 | ~spl3_4),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f319])).
% 0.22/0.57  fof(f319,plain,(
% 0.22/0.57    $false | (~spl3_2 | spl3_3 | ~spl3_4)),
% 0.22/0.57    inference(subsumption_resolution,[],[f318,f274])).
% 0.22/0.57  fof(f274,plain,(
% 0.22/0.57    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (~spl3_2 | spl3_3)),
% 0.22/0.57    inference(backward_demodulation,[],[f74,f68])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    sK0 = sK1 | ~spl3_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f67])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    spl3_2 <=> sK0 = sK1),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.57  fof(f74,plain,(
% 0.22/0.57    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f73])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    spl3_3 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.57  % (26072)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.57  fof(f318,plain,(
% 0.22/0.57    r1_tarski(k3_subset_1(sK0,sK0),sK0) | ~spl3_4),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f316])).
% 0.22/0.57  fof(f316,plain,(
% 0.22/0.57    r1_tarski(k3_subset_1(sK0,sK0),sK0) | r1_tarski(k3_subset_1(sK0,sK0),sK0) | ~spl3_4),
% 0.22/0.57    inference(resolution,[],[f309,f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(rectify,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.57    inference(nnf_transformation,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f1])).
% 0.22/0.57  fof(f1,axiom,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.57  % (26068)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  fof(f309,plain,(
% 0.22/0.57    ( ! [X0] : (r2_hidden(sK2(k3_subset_1(sK0,sK0),X0),sK0) | r1_tarski(k3_subset_1(sK0,sK0),X0)) ) | ~spl3_4),
% 0.22/0.57    inference(resolution,[],[f130,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f32])).
% 0.22/0.57  fof(f130,plain,(
% 0.22/0.57    ( ! [X1] : (~r2_hidden(X1,k3_subset_1(sK0,sK0)) | r2_hidden(X1,sK0)) ) | ~spl3_4),
% 0.22/0.57    inference(resolution,[],[f88,f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.57  fof(f88,plain,(
% 0.22/0.57    m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f87])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    spl3_4 <=> m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.57  fof(f238,plain,(
% 0.22/0.57    spl3_1 | ~spl3_3 | ~spl3_14),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f237])).
% 0.22/0.57  fof(f237,plain,(
% 0.22/0.57    $false | (spl3_1 | ~spl3_3 | ~spl3_14)),
% 0.22/0.57    inference(subsumption_resolution,[],[f213,f220])).
% 0.22/0.57  fof(f220,plain,(
% 0.22/0.57    ~r1_tarski(k1_subset_1(sK0),sK0) | (spl3_1 | ~spl3_14)),
% 0.22/0.57    inference(backward_demodulation,[],[f65,f209])).
% 0.22/0.57  fof(f209,plain,(
% 0.22/0.57    k1_subset_1(sK0) = k3_subset_1(sK0,sK0) | ~spl3_14),
% 0.22/0.57    inference(backward_demodulation,[],[f152,f199])).
% 0.22/0.57  fof(f199,plain,(
% 0.22/0.57    sK0 = sK1 | ~spl3_14),
% 0.22/0.57    inference(forward_demodulation,[],[f193,f55])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ( ! [X0] : (k3_subset_1(X0,k1_subset_1(X0)) = X0) )),
% 0.22/0.57    inference(definition_unfolding,[],[f36,f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f8])).
% 0.22/0.57  fof(f8,axiom,(
% 0.22/0.57    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.57    inference(cnf_transformation,[],[f3])).
% 0.22/0.57  fof(f3,axiom,(
% 0.22/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.57  fof(f193,plain,(
% 0.22/0.57    sK1 = k3_subset_1(sK0,k1_subset_1(sK0)) | ~spl3_14),
% 0.22/0.57    inference(backward_demodulation,[],[f117,f152])).
% 0.22/0.57  fof(f117,plain,(
% 0.22/0.57    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.22/0.57    inference(resolution,[],[f33,f41])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(flattening,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(nnf_transformation,[],[f14])).
% 0.22/0.57  fof(f14,plain,(
% 0.22/0.57    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.22/0.57    inference(negated_conjecture,[],[f12])).
% 0.22/0.57  fof(f12,conjecture,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 0.22/0.57  fof(f152,plain,(
% 0.22/0.57    k3_subset_1(sK0,sK1) = k1_subset_1(sK0) | ~spl3_14),
% 0.22/0.57    inference(avatar_component_clause,[],[f150])).
% 0.22/0.57  fof(f150,plain,(
% 0.22/0.57    spl3_14 <=> k3_subset_1(sK0,sK1) = k1_subset_1(sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f63])).
% 0.22/0.57  fof(f63,plain,(
% 0.22/0.57    spl3_1 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.57  fof(f213,plain,(
% 0.22/0.57    r1_tarski(k1_subset_1(sK0),sK0) | (~spl3_3 | ~spl3_14)),
% 0.22/0.57    inference(backward_demodulation,[],[f191,f199])).
% 0.22/0.57  fof(f191,plain,(
% 0.22/0.57    r1_tarski(k1_subset_1(sK0),sK1) | (~spl3_3 | ~spl3_14)),
% 0.22/0.57    inference(backward_demodulation,[],[f75,f152])).
% 0.22/0.57  fof(f75,plain,(
% 0.22/0.57    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f73])).
% 0.22/0.57  fof(f201,plain,(
% 0.22/0.57    spl3_2 | ~spl3_14),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f200])).
% 0.22/0.57  fof(f200,plain,(
% 0.22/0.57    $false | (spl3_2 | ~spl3_14)),
% 0.22/0.57    inference(subsumption_resolution,[],[f199,f69])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    sK0 != sK1 | spl3_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f67])).
% 0.22/0.57  fof(f190,plain,(
% 0.22/0.57    spl3_11),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f189])).
% 0.22/0.57  fof(f189,plain,(
% 0.22/0.57    $false | spl3_11),
% 0.22/0.57    inference(subsumption_resolution,[],[f188,f33])).
% 0.22/0.57  fof(f188,plain,(
% 0.22/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_11),
% 0.22/0.57    inference(resolution,[],[f139,f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.57  fof(f139,plain,(
% 0.22/0.57    ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl3_11),
% 0.22/0.57    inference(avatar_component_clause,[],[f137])).
% 0.22/0.57  fof(f137,plain,(
% 0.22/0.57    spl3_11 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.57  fof(f153,plain,(
% 0.22/0.57    ~spl3_11 | spl3_14 | ~spl3_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f148,f73,f150,f137])).
% 0.22/0.57  fof(f148,plain,(
% 0.22/0.57    k3_subset_1(sK0,sK1) = k1_subset_1(sK0) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.22/0.57    inference(subsumption_resolution,[],[f134,f75])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | k3_subset_1(sK0,sK1) = k1_subset_1(sK0) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.57    inference(superposition,[],[f42,f117])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.57    inference(cnf_transformation,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X1] : (((r1_tarski(X1,k3_subset_1(X0,X1)) | k1_subset_1(X0) != X1) & (k1_subset_1(X0) = X1 | ~r1_tarski(X1,k3_subset_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(nnf_transformation,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,axiom,(
% 0.22/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.22/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.22/0.57  fof(f114,plain,(
% 0.22/0.57    ~spl3_2 | spl3_4),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f113])).
% 0.22/0.57  fof(f113,plain,(
% 0.22/0.57    $false | (~spl3_2 | spl3_4)),
% 0.22/0.57    inference(subsumption_resolution,[],[f112,f78])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.22/0.57    inference(backward_demodulation,[],[f33,f68])).
% 0.22/0.57  fof(f112,plain,(
% 0.22/0.57    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_4),
% 0.22/0.57    inference(resolution,[],[f89,f40])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    ~m1_subset_1(k3_subset_1(sK0,sK0),k1_zfmisc_1(sK0)) | spl3_4),
% 0.22/0.57    inference(avatar_component_clause,[],[f87])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    spl3_3 | spl3_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f71,f67,f73])).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.57    inference(forward_demodulation,[],[f54,f55])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    sK1 = k3_subset_1(sK0,k1_subset_1(sK0)) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.57    inference(definition_unfolding,[],[f34,f39])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    ~spl3_1 | ~spl3_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f61,f67,f63])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.22/0.57    inference(inner_rewriting,[],[f60])).
% 0.22/0.57  fof(f60,plain,(
% 0.22/0.57    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.57    inference(forward_demodulation,[],[f53,f55])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    sK1 != k3_subset_1(sK0,k1_subset_1(sK0)) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.57    inference(definition_unfolding,[],[f35,f39])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (26050)------------------------------
% 0.22/0.57  % (26050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (26050)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (26050)Memory used [KB]: 10746
% 0.22/0.57  % (26050)Time elapsed: 0.162 s
% 0.22/0.57  % (26050)------------------------------
% 0.22/0.57  % (26050)------------------------------
% 1.58/0.57  % (26040)Success in time 0.208 s
%------------------------------------------------------------------------------
