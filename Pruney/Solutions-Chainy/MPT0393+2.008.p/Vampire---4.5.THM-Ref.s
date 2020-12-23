%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:52 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 150 expanded)
%              Number of leaves         :   19 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :  225 ( 421 expanded)
%              Number of equality atoms :   68 ( 164 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f617,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f293,f441,f567,f585,f616])).

fof(f616,plain,
    ( ~ spl8_5
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | ~ spl8_5
    | spl8_8 ),
    inference(resolution,[],[f607,f113])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f607,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ spl8_5
    | spl8_8 ),
    inference(backward_demodulation,[],[f584,f603])).

fof(f603,plain,
    ( sK2 = sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2)
    | ~ spl8_5 ),
    inference(resolution,[],[f292,f117])).

fof(f117,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f71,f102])).

fof(f102,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f101])).

fof(f101,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f292,plain,
    ( r2_hidden(sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2),k2_enumset1(sK2,sK2,sK2,sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl8_5
  <=> r2_hidden(sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f584,plain,
    ( ~ r1_tarski(sK2,sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f582])).

fof(f582,plain,
    ( spl8_8
  <=> r1_tarski(sK2,sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f585,plain,
    ( ~ spl8_8
    | spl8_4
    | spl8_1 ),
    inference(avatar_split_clause,[],[f577,f130,f285,f582])).

fof(f285,plain,
    ( spl8_4
  <=> k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f130,plain,
    ( spl8_1
  <=> r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f577,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ r1_tarski(sK2,sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2))
    | spl8_1 ),
    inference(resolution,[],[f132,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X1,sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK3(X0,X1))
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f132,plain,
    ( ~ r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f567,plain,
    ( spl8_1
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f565])).

fof(f565,plain,
    ( $false
    | spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f563,f545])).

fof(f545,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_setfam_1(k1_xboole_0)))
    | spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f531,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f531,plain,
    ( ~ r1_tarski(sK2,k1_setfam_1(k1_xboole_0))
    | spl8_1
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f132,f287])).

fof(f287,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f285])).

fof(f563,plain,
    ( ! [X0] : m1_subset_1(sK2,X0)
    | ~ spl8_4 ),
    inference(resolution,[],[f561,f210])).

fof(f210,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f79,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f561,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl8_4 ),
    inference(superposition,[],[f116,f287])).

fof(f116,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f72,f102])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f441,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | spl8_2 ),
    inference(resolution,[],[f217,f136])).

fof(f136,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl8_2
  <=> r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f217,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0) ),
    inference(resolution,[],[f193,f116])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(k1_setfam_1(X0),X1) ) ),
    inference(resolution,[],[f78,f113])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(k1_setfam_1(X1),X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f293,plain,
    ( spl8_5
    | spl8_4
    | spl8_1 ),
    inference(avatar_split_clause,[],[f280,f130,f285,f290])).

fof(f280,plain,
    ( k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)
    | r2_hidden(sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2),k2_enumset1(sK2,sK2,sK2,sK2))
    | spl8_1 ),
    inference(resolution,[],[f63,f132])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f138,plain,
    ( ~ spl8_2
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f125,f130,f134])).

fof(f125,plain,
    ( ~ r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))
    | ~ r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2) ),
    inference(extensionality_resolution,[],[f67,f103])).

fof(f103,plain,(
    sK2 != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f59,f102])).

fof(f59,plain,(
    sK2 != k1_setfam_1(k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    sK2 != k1_setfam_1(k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f30])).

fof(f30,plain,
    ( ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0
   => sK2 != k1_setfam_1(k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 11:43:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (23264)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (23261)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (23288)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (23261)Refutation not found, incomplete strategy% (23261)------------------------------
% 0.21/0.51  % (23261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23262)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (23261)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23261)Memory used [KB]: 10746
% 0.21/0.51  % (23261)Time elapsed: 0.093 s
% 0.21/0.51  % (23261)------------------------------
% 0.21/0.51  % (23261)------------------------------
% 0.21/0.51  % (23269)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (23265)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.51  % (23282)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.51  % (23269)Refutation not found, incomplete strategy% (23269)------------------------------
% 1.20/0.51  % (23269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (23269)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.51  
% 1.20/0.51  % (23269)Memory used [KB]: 10618
% 1.20/0.51  % (23269)Time elapsed: 0.107 s
% 1.20/0.51  % (23269)------------------------------
% 1.20/0.51  % (23269)------------------------------
% 1.20/0.52  % (23272)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.20/0.52  % (23289)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.20/0.52  % (23266)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.20/0.52  % (23274)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.20/0.53  % (23281)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.20/0.53  % (23267)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.20/0.53  % (23281)Refutation not found, incomplete strategy% (23281)------------------------------
% 1.20/0.53  % (23281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (23281)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (23281)Memory used [KB]: 1663
% 1.20/0.53  % (23281)Time elapsed: 0.125 s
% 1.20/0.53  % (23281)------------------------------
% 1.20/0.53  % (23281)------------------------------
% 1.20/0.53  % (23267)Refutation not found, incomplete strategy% (23267)------------------------------
% 1.20/0.53  % (23267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.53  % (23267)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.53  
% 1.20/0.53  % (23267)Memory used [KB]: 10618
% 1.20/0.53  % (23267)Time elapsed: 0.116 s
% 1.20/0.53  % (23267)------------------------------
% 1.20/0.53  % (23267)------------------------------
% 1.20/0.53  % (23263)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.53  % (23283)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.34/0.53  % (23283)Refutation not found, incomplete strategy% (23283)------------------------------
% 1.34/0.53  % (23283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (23283)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (23283)Memory used [KB]: 1791
% 1.34/0.53  % (23283)Time elapsed: 0.074 s
% 1.34/0.53  % (23283)------------------------------
% 1.34/0.53  % (23283)------------------------------
% 1.34/0.53  % (23270)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (23277)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.34/0.54  % (23278)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.34/0.54  % (23259)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.54  % (23259)Refutation not found, incomplete strategy% (23259)------------------------------
% 1.34/0.54  % (23259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (23259)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (23259)Memory used [KB]: 1663
% 1.34/0.54  % (23259)Time elapsed: 0.126 s
% 1.34/0.54  % (23259)------------------------------
% 1.34/0.54  % (23259)------------------------------
% 1.34/0.54  % (23260)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.54  % (23286)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.54  % (23279)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.34/0.55  % (23287)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.34/0.55  % (23271)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.55  % (23268)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.55  % (23273)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.34/0.55  % (23284)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.55  % (23276)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.56  % (23270)Refutation not found, incomplete strategy% (23270)------------------------------
% 1.34/0.56  % (23270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (23270)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (23270)Memory used [KB]: 10746
% 1.34/0.56  % (23270)Time elapsed: 0.140 s
% 1.34/0.56  % (23270)------------------------------
% 1.34/0.56  % (23270)------------------------------
% 1.34/0.56  % (23285)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.56  % (23275)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.57  % (23279)Refutation not found, incomplete strategy% (23279)------------------------------
% 1.34/0.57  % (23279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.57  % (23279)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.57  
% 1.34/0.57  % (23279)Memory used [KB]: 10746
% 1.34/0.57  % (23279)Time elapsed: 0.136 s
% 1.34/0.57  % (23279)------------------------------
% 1.34/0.57  % (23279)------------------------------
% 1.34/0.60  % (23271)Refutation found. Thanks to Tanya!
% 1.34/0.60  % SZS status Theorem for theBenchmark
% 1.34/0.60  % SZS output start Proof for theBenchmark
% 1.34/0.60  fof(f617,plain,(
% 1.34/0.60    $false),
% 1.34/0.60    inference(avatar_sat_refutation,[],[f138,f293,f441,f567,f585,f616])).
% 1.34/0.60  fof(f616,plain,(
% 1.34/0.60    ~spl8_5 | spl8_8),
% 1.34/0.60    inference(avatar_contradiction_clause,[],[f613])).
% 1.34/0.60  fof(f613,plain,(
% 1.34/0.60    $false | (~spl8_5 | spl8_8)),
% 1.34/0.60    inference(resolution,[],[f607,f113])).
% 1.34/0.60  fof(f113,plain,(
% 1.34/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.34/0.60    inference(equality_resolution,[],[f66])).
% 1.34/0.60  fof(f66,plain,(
% 1.34/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.34/0.60    inference(cnf_transformation,[],[f35])).
% 1.34/0.60  fof(f35,plain,(
% 1.34/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.60    inference(flattening,[],[f34])).
% 1.34/0.60  fof(f34,plain,(
% 1.34/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.60    inference(nnf_transformation,[],[f3])).
% 1.34/0.60  fof(f3,axiom,(
% 1.34/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.60  fof(f607,plain,(
% 1.34/0.60    ~r1_tarski(sK2,sK2) | (~spl8_5 | spl8_8)),
% 1.34/0.60    inference(backward_demodulation,[],[f584,f603])).
% 1.34/0.60  fof(f603,plain,(
% 1.34/0.60    sK2 = sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2) | ~spl8_5),
% 1.34/0.60    inference(resolution,[],[f292,f117])).
% 1.34/0.60  fof(f117,plain,(
% 1.34/0.60    ( ! [X0,X3] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) | X0 = X3) )),
% 1.34/0.60    inference(equality_resolution,[],[f107])).
% 1.34/0.60  fof(f107,plain,(
% 1.34/0.60    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.34/0.60    inference(definition_unfolding,[],[f71,f102])).
% 1.34/0.60  fof(f102,plain,(
% 1.34/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.34/0.60    inference(definition_unfolding,[],[f61,f101])).
% 1.34/0.60  fof(f101,plain,(
% 1.34/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.34/0.60    inference(definition_unfolding,[],[f62,f77])).
% 1.34/0.60  fof(f77,plain,(
% 1.34/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.34/0.60    inference(cnf_transformation,[],[f8])).
% 1.34/0.60  fof(f8,axiom,(
% 1.34/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.60  fof(f62,plain,(
% 1.34/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.34/0.60    inference(cnf_transformation,[],[f7])).
% 1.34/0.60  fof(f7,axiom,(
% 1.34/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.60  fof(f61,plain,(
% 1.34/0.60    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.34/0.60    inference(cnf_transformation,[],[f6])).
% 1.34/0.60  fof(f6,axiom,(
% 1.34/0.60    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.60  fof(f71,plain,(
% 1.34/0.60    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.34/0.60    inference(cnf_transformation,[],[f43])).
% 1.34/0.60  fof(f43,plain,(
% 1.34/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.34/0.60  fof(f42,plain,(
% 1.34/0.60    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.34/0.60    introduced(choice_axiom,[])).
% 1.34/0.60  fof(f41,plain,(
% 1.34/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.60    inference(rectify,[],[f40])).
% 1.34/0.60  fof(f40,plain,(
% 1.34/0.60    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.34/0.60    inference(nnf_transformation,[],[f5])).
% 1.34/0.60  fof(f5,axiom,(
% 1.34/0.60    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.34/0.60  fof(f292,plain,(
% 1.34/0.60    r2_hidden(sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2),k2_enumset1(sK2,sK2,sK2,sK2)) | ~spl8_5),
% 1.34/0.60    inference(avatar_component_clause,[],[f290])).
% 1.34/0.60  fof(f290,plain,(
% 1.34/0.60    spl8_5 <=> r2_hidden(sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2),k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.34/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.34/0.60  fof(f584,plain,(
% 1.34/0.60    ~r1_tarski(sK2,sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2)) | spl8_8),
% 1.34/0.60    inference(avatar_component_clause,[],[f582])).
% 1.34/0.60  fof(f582,plain,(
% 1.34/0.60    spl8_8 <=> r1_tarski(sK2,sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2))),
% 1.34/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.34/0.60  fof(f585,plain,(
% 1.34/0.60    ~spl8_8 | spl8_4 | spl8_1),
% 1.34/0.60    inference(avatar_split_clause,[],[f577,f130,f285,f582])).
% 1.34/0.60  fof(f285,plain,(
% 1.34/0.60    spl8_4 <=> k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2)),
% 1.34/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.34/0.60  fof(f130,plain,(
% 1.34/0.60    spl8_1 <=> r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)))),
% 1.34/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.34/0.60  fof(f577,plain,(
% 1.34/0.60    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~r1_tarski(sK2,sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2)) | spl8_1),
% 1.34/0.60    inference(resolution,[],[f132,f64])).
% 1.34/0.60  fof(f64,plain,(
% 1.34/0.60    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X1,sK3(X0,X1))) )),
% 1.34/0.60    inference(cnf_transformation,[],[f33])).
% 1.34/0.60  fof(f33,plain,(
% 1.34/0.60    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 1.34/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f32])).
% 1.34/0.60  fof(f32,plain,(
% 1.34/0.60    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK3(X0,X1)) & r2_hidden(sK3(X0,X1),X0)))),
% 1.34/0.60    introduced(choice_axiom,[])).
% 1.34/0.60  fof(f19,plain,(
% 1.34/0.60    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.34/0.60    inference(flattening,[],[f18])).
% 1.34/0.60  fof(f18,plain,(
% 1.34/0.60    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.34/0.60    inference(ennf_transformation,[],[f13])).
% 1.34/0.60  fof(f13,axiom,(
% 1.34/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 1.34/0.60  fof(f132,plain,(
% 1.34/0.60    ~r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))) | spl8_1),
% 1.34/0.60    inference(avatar_component_clause,[],[f130])).
% 1.34/0.60  fof(f567,plain,(
% 1.34/0.60    spl8_1 | ~spl8_4),
% 1.34/0.60    inference(avatar_contradiction_clause,[],[f565])).
% 1.34/0.60  fof(f565,plain,(
% 1.34/0.60    $false | (spl8_1 | ~spl8_4)),
% 1.34/0.60    inference(resolution,[],[f563,f545])).
% 1.34/0.60  fof(f545,plain,(
% 1.34/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k1_setfam_1(k1_xboole_0))) | (spl8_1 | ~spl8_4)),
% 1.34/0.60    inference(resolution,[],[f531,f75])).
% 1.34/0.60  fof(f75,plain,(
% 1.34/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.34/0.60    inference(cnf_transformation,[],[f44])).
% 1.34/0.60  fof(f44,plain,(
% 1.34/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.34/0.60    inference(nnf_transformation,[],[f11])).
% 1.34/0.60  fof(f11,axiom,(
% 1.34/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.34/0.60  fof(f531,plain,(
% 1.34/0.60    ~r1_tarski(sK2,k1_setfam_1(k1_xboole_0)) | (spl8_1 | ~spl8_4)),
% 1.34/0.60    inference(forward_demodulation,[],[f132,f287])).
% 1.34/0.60  fof(f287,plain,(
% 1.34/0.60    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | ~spl8_4),
% 1.34/0.60    inference(avatar_component_clause,[],[f285])).
% 1.34/0.60  fof(f563,plain,(
% 1.34/0.60    ( ! [X0] : (m1_subset_1(sK2,X0)) ) | ~spl8_4),
% 1.34/0.60    inference(resolution,[],[f561,f210])).
% 1.34/0.60  fof(f210,plain,(
% 1.34/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | m1_subset_1(X0,X1)) )),
% 1.34/0.60    inference(resolution,[],[f79,f60])).
% 1.34/0.60  fof(f60,plain,(
% 1.34/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.34/0.60    inference(cnf_transformation,[],[f10])).
% 1.34/0.60  fof(f10,axiom,(
% 1.34/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.34/0.60  fof(f79,plain,(
% 1.34/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.34/0.60    inference(cnf_transformation,[],[f24])).
% 1.34/0.60  fof(f24,plain,(
% 1.34/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.34/0.60    inference(flattening,[],[f23])).
% 1.34/0.60  fof(f23,plain,(
% 1.34/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.34/0.60    inference(ennf_transformation,[],[f12])).
% 1.34/0.60  fof(f12,axiom,(
% 1.34/0.60    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.34/0.60  fof(f561,plain,(
% 1.34/0.60    r2_hidden(sK2,k1_xboole_0) | ~spl8_4),
% 1.34/0.60    inference(superposition,[],[f116,f287])).
% 1.34/0.60  fof(f116,plain,(
% 1.34/0.60    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 1.34/0.60    inference(equality_resolution,[],[f115])).
% 1.34/0.60  fof(f115,plain,(
% 1.34/0.60    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 1.34/0.60    inference(equality_resolution,[],[f106])).
% 1.34/0.60  fof(f106,plain,(
% 1.34/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.34/0.60    inference(definition_unfolding,[],[f72,f102])).
% 1.34/0.60  fof(f72,plain,(
% 1.34/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.34/0.60    inference(cnf_transformation,[],[f43])).
% 1.34/0.60  fof(f441,plain,(
% 1.34/0.60    spl8_2),
% 1.34/0.60    inference(avatar_contradiction_clause,[],[f429])).
% 1.34/0.60  fof(f429,plain,(
% 1.34/0.60    $false | spl8_2),
% 1.34/0.60    inference(resolution,[],[f217,f136])).
% 1.34/0.60  fof(f136,plain,(
% 1.34/0.60    ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2) | spl8_2),
% 1.34/0.60    inference(avatar_component_clause,[],[f134])).
% 1.34/0.60  fof(f134,plain,(
% 1.34/0.60    spl8_2 <=> r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2)),
% 1.34/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.34/0.60  fof(f217,plain,(
% 1.34/0.60    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X0)),X0)) )),
% 1.34/0.60    inference(resolution,[],[f193,f116])).
% 1.34/0.60  fof(f193,plain,(
% 1.34/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | r1_tarski(k1_setfam_1(X0),X1)) )),
% 1.34/0.60    inference(resolution,[],[f78,f113])).
% 1.34/0.60  fof(f78,plain,(
% 1.34/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(k1_setfam_1(X1),X2) | ~r2_hidden(X0,X1)) )),
% 1.34/0.60    inference(cnf_transformation,[],[f22])).
% 1.34/0.60  fof(f22,plain,(
% 1.34/0.60    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 1.34/0.60    inference(flattening,[],[f21])).
% 1.34/0.60  fof(f21,plain,(
% 1.34/0.60    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 1.34/0.60    inference(ennf_transformation,[],[f14])).
% 1.34/0.60  fof(f14,axiom,(
% 1.34/0.60    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
% 1.34/0.60  fof(f293,plain,(
% 1.34/0.60    spl8_5 | spl8_4 | spl8_1),
% 1.34/0.60    inference(avatar_split_clause,[],[f280,f130,f285,f290])).
% 1.34/0.60  fof(f280,plain,(
% 1.34/0.60    k1_xboole_0 = k2_enumset1(sK2,sK2,sK2,sK2) | r2_hidden(sK3(k2_enumset1(sK2,sK2,sK2,sK2),sK2),k2_enumset1(sK2,sK2,sK2,sK2)) | spl8_1),
% 1.34/0.60    inference(resolution,[],[f63,f132])).
% 1.34/0.60  fof(f63,plain,(
% 1.34/0.60    ( ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 1.34/0.60    inference(cnf_transformation,[],[f33])).
% 1.34/0.60  fof(f138,plain,(
% 1.34/0.60    ~spl8_2 | ~spl8_1),
% 1.34/0.60    inference(avatar_split_clause,[],[f125,f130,f134])).
% 1.34/0.60  fof(f125,plain,(
% 1.34/0.60    ~r1_tarski(sK2,k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))) | ~r1_tarski(k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2)),sK2)),
% 1.34/0.60    inference(extensionality_resolution,[],[f67,f103])).
% 1.34/0.60  fof(f103,plain,(
% 1.34/0.60    sK2 != k1_setfam_1(k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.34/0.60    inference(definition_unfolding,[],[f59,f102])).
% 1.34/0.60  fof(f59,plain,(
% 1.34/0.60    sK2 != k1_setfam_1(k1_tarski(sK2))),
% 1.34/0.60    inference(cnf_transformation,[],[f31])).
% 1.34/0.60  fof(f31,plain,(
% 1.34/0.60    sK2 != k1_setfam_1(k1_tarski(sK2))),
% 1.34/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f30])).
% 1.34/0.60  fof(f30,plain,(
% 1.34/0.60    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0 => sK2 != k1_setfam_1(k1_tarski(sK2))),
% 1.34/0.60    introduced(choice_axiom,[])).
% 1.34/0.60  fof(f17,plain,(
% 1.34/0.60    ? [X0] : k1_setfam_1(k1_tarski(X0)) != X0),
% 1.34/0.60    inference(ennf_transformation,[],[f16])).
% 1.34/0.60  fof(f16,negated_conjecture,(
% 1.34/0.60    ~! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.34/0.60    inference(negated_conjecture,[],[f15])).
% 1.34/0.60  fof(f15,conjecture,(
% 1.34/0.60    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.34/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.34/0.60  fof(f67,plain,(
% 1.34/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.34/0.60    inference(cnf_transformation,[],[f35])).
% 1.34/0.60  % SZS output end Proof for theBenchmark
% 1.34/0.60  % (23271)------------------------------
% 1.34/0.60  % (23271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.60  % (23271)Termination reason: Refutation
% 1.34/0.60  
% 1.34/0.60  % (23271)Memory used [KB]: 6524
% 1.34/0.60  % (23271)Time elapsed: 0.186 s
% 1.34/0.60  % (23271)------------------------------
% 1.34/0.60  % (23271)------------------------------
% 1.34/0.60  % (23254)Success in time 0.238 s
%------------------------------------------------------------------------------
