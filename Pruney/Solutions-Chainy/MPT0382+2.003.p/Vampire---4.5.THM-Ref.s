%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 166 expanded)
%              Number of leaves         :   17 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  230 ( 550 expanded)
%              Number of equality atoms :   49 ( 140 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f219,f222,f238,f249])).

fof(f249,plain,
    ( ~ spl4_6
    | spl4_9
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f247,f50,f46,f42,f236,f217])).

fof(f217,plain,
    ( spl4_6
  <=> r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f236,plain,
    ( spl4_9
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f42,plain,
    ( spl4_2
  <=> k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f46,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f50,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f247,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f209,f51])).

fof(f51,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f209,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r1_tarski(X0,sK2)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X0)) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f207,f43])).

fof(f43,plain,
    ( k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0))
        | r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f30,f47])).

fof(f47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

fof(f238,plain,
    ( ~ spl4_9
    | spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f228,f214,f38,f236])).

fof(f38,plain,
    ( spl4_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f214,plain,
    ( spl4_5
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f228,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f215,f97])).

fof(f97,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | X2 = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f96,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(global_subsumption,[],[f57,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0)
      | k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f35,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X2),X1)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK3(X0,X1,X2),X0)
        & r1_tarski(sK3(X0,X1,X2),X2)
        & r1_tarski(sK3(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK3(X0,X1,X2),X0)
        & r1_tarski(sK3(X0,X1,X2),X2)
        & r1_tarski(sK3(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(trivial_inequality_removal,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f55,f28])).

fof(f28,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f54,f27])).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_tarski(X0,X2)
      | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X2,X1)) ) ),
    inference(resolution,[],[f36,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f96,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X2) ) ),
    inference(global_subsumption,[],[f57,f93])).

fof(f93,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2)
      | k3_xboole_0(X2,X3) = X3
      | ~ r1_tarski(X3,X3)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f35,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f215,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f214])).

fof(f222,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | spl4_6 ),
    inference(resolution,[],[f218,f57])).

fof(f218,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f212,f50,f46,f42,f217,f214])).

fof(f212,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))
    | r1_tarski(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f210,f43])).

fof(f210,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f208,f47])).

fof(f208,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r1_tarski(X1,sK1)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X1)) )
    | ~ spl4_4 ),
    inference(resolution,[],[f30,f51])).

fof(f52,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != sK2
    & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(X0,X2) = k3_subset_1(X0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & k3_subset_1(sK0,X2) = k3_subset_1(sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k3_subset_1(sK0,X2) = k3_subset_1(sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != sK2
      & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X2) = k3_subset_1(X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & k3_subset_1(X0,X2) = k3_subset_1(X0,X1)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( k3_subset_1(X0,X2) = k3_subset_1(X0,X1)
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X2) = k3_subset_1(X0,X1)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).

fof(f48,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f42])).

fof(f25,plain,(
    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f26,f38])).

fof(f26,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (11539)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (11526)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (11526)Refutation not found, incomplete strategy% (11526)------------------------------
% 0.21/0.47  % (11526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (11526)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (11526)Memory used [KB]: 10618
% 0.21/0.47  % (11526)Time elapsed: 0.062 s
% 0.21/0.47  % (11526)------------------------------
% 0.21/0.47  % (11526)------------------------------
% 0.21/0.47  % (11531)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (11533)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (11537)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (11537)Refutation not found, incomplete strategy% (11537)------------------------------
% 0.21/0.49  % (11537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11537)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11537)Memory used [KB]: 6140
% 0.21/0.49  % (11537)Time elapsed: 0.078 s
% 0.21/0.49  % (11537)------------------------------
% 0.21/0.49  % (11537)------------------------------
% 0.21/0.49  % (11531)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f40,f44,f48,f52,f219,f222,f238,f249])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    ~spl4_6 | spl4_9 | ~spl4_2 | ~spl4_3 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f247,f50,f46,f42,f236,f217])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    spl4_6 <=> r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    spl4_9 <=> r1_tarski(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl4_2 <=> k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2) | ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.21/0.49    inference(resolution,[],[f209,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,sK2) | ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X0))) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.49    inference(forward_demodulation,[],[f207,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f42])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,X0)) | r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl4_3),
% 0.21/0.49    inference(resolution,[],[f30,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f46])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(nnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    ~spl4_9 | spl4_1 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f228,f214,f38,f236])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    spl4_1 <=> sK1 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    spl4_5 <=> r1_tarski(sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    sK1 = sK2 | ~r1_tarski(sK1,sK2) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f215,f97])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r1_tarski(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3)) )),
% 0.21/0.49    inference(superposition,[],[f96,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(global_subsumption,[],[f57,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0)) )),
% 0.21/0.49    inference(resolution,[],[f35,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(sK3(X0,X1,X2),X1) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK3(X0,X1,X2),X0) & r1_tarski(sK3(X0,X1,X2),X2) & r1_tarski(sK3(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK3(X0,X1,X2),X0) & r1_tarski(sK3(X0,X1,X2),X2) & r1_tarski(sK3(X0,X1,X2),X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(sK3(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,X0)) )),
% 0.21/0.49    inference(superposition,[],[f55,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f54,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_tarski(X0,X2) | k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X2,X1))) )),
% 0.21/0.49    inference(resolution,[],[f36,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X2)) )),
% 0.21/0.49    inference(global_subsumption,[],[f57,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2) | k3_xboole_0(X2,X3) = X3 | ~r1_tarski(X3,X3) | ~r1_tarski(X3,X2)) )),
% 0.21/0.49    inference(resolution,[],[f35,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(sK3(X0,X1,X2),X2) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    r1_tarski(sK2,sK1) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f214])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f221])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    $false | spl4_6),
% 0.21/0.49    inference(resolution,[],[f218,f57])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) | spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f217])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    spl4_5 | ~spl4_6 | ~spl4_2 | ~spl4_3 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f212,f50,f46,f42,f217,f214])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1)) | r1_tarski(sK2,sK1) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.21/0.49    inference(forward_demodulation,[],[f210,f43])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    r1_tarski(sK2,sK1) | ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK2)) | (~spl4_3 | ~spl4_4)),
% 0.21/0.49    inference(resolution,[],[f208,f47])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r1_tarski(X1,sK1) | ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X1))) ) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f30,f51])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f50])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    (sK1 != sK2 & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (X1 != X2 & k3_subset_1(X0,X2) = k3_subset_1(X0,X1) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != X2 & k3_subset_1(sK0,X2) = k3_subset_1(sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X2] : (sK1 != X2 & k3_subset_1(sK0,X2) = k3_subset_1(sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != sK2 & k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (X1 != X2 & k3_subset_1(X0,X2) = k3_subset_1(X0,X1) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((X1 != X2 & k3_subset_1(X0,X2) = k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (k3_subset_1(X0,X2) = k3_subset_1(X0,X1) => X1 = X2)))),
% 0.21/0.49    inference(negated_conjecture,[],[f7])).
% 0.21/0.49  fof(f7,conjecture,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (k3_subset_1(X0,X2) = k3_subset_1(X0,X1) => X1 = X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f46])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f42])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f38])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    sK1 != sK2),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (11531)------------------------------
% 0.21/0.49  % (11531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11531)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (11531)Memory used [KB]: 10746
% 0.21/0.49  % (11531)Time elapsed: 0.034 s
% 0.21/0.49  % (11531)------------------------------
% 0.21/0.49  % (11531)------------------------------
% 0.21/0.49  % (11524)Success in time 0.137 s
%------------------------------------------------------------------------------
