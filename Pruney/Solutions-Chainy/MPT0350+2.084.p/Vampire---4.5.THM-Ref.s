%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:02 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 113 expanded)
%              Number of leaves         :   22 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  159 ( 231 expanded)
%              Number of equality atoms :   46 (  64 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f70,f82,f133,f140,f150,f151])).

% (18124)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f151,plain,
    ( sK0 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1)))
    | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1)))
    | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f150,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f149,f130,f72,f145])).

fof(f145,plain,
    ( spl3_12
  <=> sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f72,plain,
    ( spl3_4
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f130,plain,
    ( spl3_11
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f149,plain,
    ( sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1)))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f142,f74])).

fof(f74,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f142,plain,
    ( sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))
    | ~ spl3_11 ),
    inference(resolution,[],[f132,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f42,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f132,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f130])).

fof(f140,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f136,f67,f53,f112])).

fof(f112,plain,
    ( spl3_9
  <=> k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f53,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f67,plain,
    ( spl3_3
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f136,plain,
    ( k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f61,f69])).

fof(f69,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f55,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f133,plain,
    ( spl3_11
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f128,f53,f130])).

fof(f128,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f84,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f84,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(sK1,X2),sK0)
        | r1_tarski(sK1,X2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f63,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | r2_hidden(X2,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f82,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f64,f53,f72])).

fof(f64,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f55,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f35,f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f70,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f60,f53,f67])).

fof(f60,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f27,f53])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

% (18142)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f15,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f51,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f46,f48])).

fof(f48,plain,
    ( spl3_1
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f46,plain,(
    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f28,f29])).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f28,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:05:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (18128)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (18121)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (18123)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.23/0.51  % (18119)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.52  % (18132)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.52  % (18135)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.23/0.52  % (18144)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.23/0.52  % (18139)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.23/0.52  % (18144)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % (18136)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.23/0.52  % (18134)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.23/0.52  % (18141)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.23/0.52  % (18127)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.23/0.53  % (18143)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.23/0.53  % (18131)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.53  % (18133)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.53  % (18126)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.23/0.53  % (18122)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.53  % (18136)Refutation not found, incomplete strategy% (18136)------------------------------
% 1.23/0.53  % (18136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (18136)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (18136)Memory used [KB]: 10618
% 1.23/0.53  % (18136)Time elapsed: 0.115 s
% 1.23/0.53  % (18136)------------------------------
% 1.23/0.53  % (18136)------------------------------
% 1.23/0.53  % (18140)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.53  % (18125)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.39/0.53  % SZS output start Proof for theBenchmark
% 1.39/0.53  fof(f152,plain,(
% 1.39/0.53    $false),
% 1.39/0.53    inference(avatar_sat_refutation,[],[f51,f56,f70,f82,f133,f140,f150,f151])).
% 1.39/0.53  % (18124)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.53  fof(f151,plain,(
% 1.39/0.53    sK0 != k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) | k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) != k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.39/0.53    introduced(theory_tautology_sat_conflict,[])).
% 1.39/0.53  fof(f150,plain,(
% 1.39/0.53    spl3_12 | ~spl3_4 | ~spl3_11),
% 1.39/0.53    inference(avatar_split_clause,[],[f149,f130,f72,f145])).
% 1.39/0.53  fof(f145,plain,(
% 1.39/0.53    spl3_12 <=> sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1)))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.39/0.53  fof(f72,plain,(
% 1.39/0.53    spl3_4 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.39/0.53  fof(f130,plain,(
% 1.39/0.53    spl3_11 <=> r1_tarski(sK1,sK0)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.39/0.53  fof(f149,plain,(
% 1.39/0.53    sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) | (~spl3_4 | ~spl3_11)),
% 1.39/0.53    inference(forward_demodulation,[],[f142,f74])).
% 1.39/0.53  fof(f74,plain,(
% 1.39/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_4),
% 1.39/0.53    inference(avatar_component_clause,[],[f72])).
% 1.39/0.53  fof(f142,plain,(
% 1.39/0.53    sK0 = k3_tarski(k2_enumset1(sK1,sK1,sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))) | ~spl3_11),
% 1.39/0.53    inference(resolution,[],[f132,f43])).
% 1.39/0.53  fof(f43,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f33,f42,f32])).
% 1.39/0.53  fof(f32,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f2])).
% 1.39/0.53  fof(f2,axiom,(
% 1.39/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.39/0.53  fof(f42,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.39/0.53    inference(definition_unfolding,[],[f30,f41])).
% 1.39/0.53  fof(f41,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f31,f39])).
% 1.39/0.53  fof(f39,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f5])).
% 1.39/0.53  fof(f5,axiom,(
% 1.39/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.39/0.53  fof(f31,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f4])).
% 1.39/0.53  fof(f4,axiom,(
% 1.39/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.39/0.53  fof(f30,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f6])).
% 1.39/0.53  fof(f6,axiom,(
% 1.39/0.53    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.39/0.53  fof(f33,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f16])).
% 1.39/0.53  fof(f16,plain,(
% 1.39/0.53    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.39/0.53    inference(ennf_transformation,[],[f3])).
% 1.39/0.53  fof(f3,axiom,(
% 1.39/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.39/0.53  fof(f132,plain,(
% 1.39/0.53    r1_tarski(sK1,sK0) | ~spl3_11),
% 1.39/0.53    inference(avatar_component_clause,[],[f130])).
% 1.39/0.53  fof(f140,plain,(
% 1.39/0.53    spl3_9 | ~spl3_2 | ~spl3_3),
% 1.39/0.53    inference(avatar_split_clause,[],[f136,f67,f53,f112])).
% 1.39/0.53  fof(f112,plain,(
% 1.39/0.53    spl3_9 <=> k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1)))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.39/0.53  fof(f53,plain,(
% 1.39/0.53    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.39/0.53  fof(f67,plain,(
% 1.39/0.53    spl3_3 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.39/0.53  fof(f136,plain,(
% 1.39/0.53    k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k3_subset_1(sK0,sK1))) | (~spl3_2 | ~spl3_3)),
% 1.39/0.53    inference(resolution,[],[f61,f69])).
% 1.39/0.53  fof(f69,plain,(
% 1.39/0.53    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_3),
% 1.39/0.53    inference(avatar_component_clause,[],[f67])).
% 1.39/0.53  fof(f61,plain,(
% 1.39/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0))) ) | ~spl3_2),
% 1.39/0.53    inference(resolution,[],[f55,f45])).
% 1.39/0.53  fof(f45,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.39/0.53    inference(definition_unfolding,[],[f40,f42])).
% 1.39/0.53  fof(f40,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f22])).
% 1.39/0.53  fof(f22,plain,(
% 1.39/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.53    inference(flattening,[],[f21])).
% 1.39/0.53  fof(f21,plain,(
% 1.39/0.53    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.39/0.53    inference(ennf_transformation,[],[f11])).
% 1.39/0.53  fof(f11,axiom,(
% 1.39/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.39/0.53  fof(f55,plain,(
% 1.39/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.39/0.53    inference(avatar_component_clause,[],[f53])).
% 1.39/0.53  fof(f133,plain,(
% 1.39/0.53    spl3_11 | ~spl3_2),
% 1.39/0.53    inference(avatar_split_clause,[],[f128,f53,f130])).
% 1.39/0.53  fof(f128,plain,(
% 1.39/0.53    r1_tarski(sK1,sK0) | ~spl3_2),
% 1.39/0.53    inference(duplicate_literal_removal,[],[f126])).
% 1.39/0.53  fof(f126,plain,(
% 1.39/0.53    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0) | ~spl3_2),
% 1.39/0.53    inference(resolution,[],[f84,f38])).
% 1.39/0.53  fof(f38,plain,(
% 1.39/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f26])).
% 1.39/0.53  fof(f26,plain,(
% 1.39/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.39/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f25])).
% 1.39/0.53  fof(f25,plain,(
% 1.39/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.39/0.53    introduced(choice_axiom,[])).
% 1.39/0.53  fof(f20,plain,(
% 1.39/0.53    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.39/0.53    inference(ennf_transformation,[],[f14])).
% 1.39/0.53  fof(f14,plain,(
% 1.39/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.39/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 1.39/0.53  fof(f1,axiom,(
% 1.39/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.53  fof(f84,plain,(
% 1.39/0.53    ( ! [X2] : (r2_hidden(sK2(sK1,X2),sK0) | r1_tarski(sK1,X2)) ) | ~spl3_2),
% 1.39/0.53    inference(resolution,[],[f63,f37])).
% 1.39/0.53  fof(f37,plain,(
% 1.39/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f26])).
% 1.39/0.53  fof(f63,plain,(
% 1.39/0.53    ( ! [X2] : (~r2_hidden(X2,sK1) | r2_hidden(X2,sK0)) ) | ~spl3_2),
% 1.39/0.53    inference(resolution,[],[f55,f36])).
% 1.39/0.53  fof(f36,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f19])).
% 1.39/0.53  fof(f19,plain,(
% 1.39/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.53    inference(ennf_transformation,[],[f10])).
% 1.39/0.53  fof(f10,axiom,(
% 1.39/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.39/0.53  fof(f82,plain,(
% 1.39/0.53    spl3_4 | ~spl3_2),
% 1.39/0.53    inference(avatar_split_clause,[],[f64,f53,f72])).
% 1.39/0.53  fof(f64,plain,(
% 1.39/0.53    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_2),
% 1.39/0.53    inference(resolution,[],[f55,f44])).
% 1.39/0.53  fof(f44,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.39/0.53    inference(definition_unfolding,[],[f35,f32])).
% 1.39/0.53  fof(f35,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f18])).
% 1.39/0.53  fof(f18,plain,(
% 1.39/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.53    inference(ennf_transformation,[],[f8])).
% 1.39/0.53  fof(f8,axiom,(
% 1.39/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.39/0.53  fof(f70,plain,(
% 1.39/0.53    spl3_3 | ~spl3_2),
% 1.39/0.53    inference(avatar_split_clause,[],[f60,f53,f67])).
% 1.39/0.53  fof(f60,plain,(
% 1.39/0.53    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_2),
% 1.39/0.53    inference(unit_resulting_resolution,[],[f55,f34])).
% 1.39/0.53  fof(f34,plain,(
% 1.39/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f17])).
% 1.39/0.53  fof(f17,plain,(
% 1.39/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.53    inference(ennf_transformation,[],[f9])).
% 1.39/0.53  fof(f9,axiom,(
% 1.39/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.39/0.53  fof(f56,plain,(
% 1.39/0.53    spl3_2),
% 1.39/0.53    inference(avatar_split_clause,[],[f27,f53])).
% 1.39/0.53  fof(f27,plain,(
% 1.39/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.39/0.53    inference(cnf_transformation,[],[f24])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.39/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f23])).
% 1.39/0.54  fof(f23,plain,(
% 1.39/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.39/0.54    introduced(choice_axiom,[])).
% 1.39/0.54  % (18142)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.54  fof(f15,plain,(
% 1.39/0.54    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.39/0.54    inference(negated_conjecture,[],[f12])).
% 1.39/0.54  fof(f12,conjecture,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 1.39/0.54  fof(f51,plain,(
% 1.39/0.54    ~spl3_1),
% 1.39/0.54    inference(avatar_split_clause,[],[f46,f48])).
% 1.39/0.54  fof(f48,plain,(
% 1.39/0.54    spl3_1 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.39/0.54  fof(f46,plain,(
% 1.39/0.54    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.39/0.54    inference(forward_demodulation,[],[f28,f29])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.39/0.54    inference(cnf_transformation,[],[f7])).
% 1.39/0.54  fof(f7,axiom,(
% 1.39/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 1.39/0.54    inference(cnf_transformation,[],[f24])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (18144)------------------------------
% 1.39/0.54  % (18144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (18144)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (18144)Memory used [KB]: 6268
% 1.39/0.54  % (18144)Time elapsed: 0.108 s
% 1.39/0.54  % (18144)------------------------------
% 1.39/0.54  % (18144)------------------------------
% 1.39/0.54  % (18138)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.54  % (18118)Success in time 0.177 s
%------------------------------------------------------------------------------
