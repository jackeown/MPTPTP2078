%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 148 expanded)
%              Number of leaves         :   14 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  213 ( 515 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f43,f48,f53,f66,f76,f97,f114,f116,f131,f133])).

fof(f133,plain,
    ( spl3_10
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f119,f63,f50,f35,f94])).

fof(f94,plain,
    ( spl3_10
  <=> r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f35,plain,
    ( spl3_1
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f50,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f63,plain,
    ( spl3_6
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f119,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f52,f65,f36,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f36,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f65,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f52,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f131,plain,
    ( ~ spl3_4
    | ~ spl3_6
    | ~ spl3_10
    | spl3_7 ),
    inference(avatar_split_clause,[],[f125,f73,f94,f63,f50])).

fof(f73,plain,
    ( spl3_7
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f125,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_7 ),
    inference(resolution,[],[f74,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f74,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f116,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f98,f73,f50,f45,f39])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f98,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f52,f47,f75,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f75,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f47,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f114,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f99,f73,f63,f50,f94])).

fof(f99,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f52,f65,f75,f32])).

fof(f97,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f86,f63,f50,f35,f94])).

fof(f86,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f52,f37,f65,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,
    ( ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f76,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f69,f50,f45,f39,f73])).

fof(f69,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f40,f52,f47,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f66,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f55,f45,f63])).

fof(f55,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f47,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_tarski(sK1,sK2)
      | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & ( r1_tarski(sK1,sK2)
      | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,X2)
              | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,X2)
            | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & ( r1_tarski(sK1,X2)
            | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,X2)
          | ~ r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & ( r1_tarski(sK1,X2)
          | r1_xboole_0(sK1,k3_subset_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ( ~ r1_tarski(sK1,sK2)
        | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & ( r1_tarski(sK1,sK2)
        | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & ( r1_tarski(X1,X2)
            | r1_xboole_0(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f43,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f25,f39,f35])).

fof(f25,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f26,f39,f35])).

fof(f26,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (28445)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (28442)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (28440)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.49  % (28455)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.49  % (28442)Refutation not found, incomplete strategy% (28442)------------------------------
% 0.21/0.49  % (28442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28444)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (28442)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28442)Memory used [KB]: 10490
% 0.21/0.49  % (28442)Time elapsed: 0.087 s
% 0.21/0.49  % (28442)------------------------------
% 0.21/0.49  % (28442)------------------------------
% 0.21/0.50  % (28443)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (28438)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (28454)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (28450)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (28445)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f42,f43,f48,f53,f66,f76,f97,f114,f116,f131,f133])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl3_10 | ~spl3_1 | ~spl3_4 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f119,f63,f50,f35,f94])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    spl3_10 <=> r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    spl3_1 <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl3_6 <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) | (~spl3_1 | ~spl3_4 | ~spl3_6)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f52,f65,f36,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f35])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f50])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ~spl3_4 | ~spl3_6 | ~spl3_10 | spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f125,f73,f94,f63,f50])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl3_7 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_7),
% 0.21/0.50    inference(resolution,[],[f74,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f98,f73,f50,f45,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    r1_tarski(sK1,sK2) | (~spl3_3 | ~spl3_4 | ~spl3_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f52,f47,f75,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f45])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl3_10 | ~spl3_4 | ~spl3_6 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f99,f73,f63,f50,f94])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) | (~spl3_4 | ~spl3_6 | ~spl3_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f52,f65,f75,f32])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ~spl3_10 | spl3_1 | ~spl3_4 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f86,f63,f50,f35,f94])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) | (spl3_1 | ~spl3_4 | ~spl3_6)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f52,f37,f65,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f35])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl3_7 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f50,f45,f39,f73])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f40,f52,f47,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f39])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl3_6 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f45,f63])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | ~spl3_3),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f47,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f50])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X2] : ((~r1_tarski(sK1,X2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & (r1_tarski(sK1,X2) | r1_xboole_0(sK1,k3_subset_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => ((~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & (r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,X2) | ~r1_xboole_0(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1] : (? [X2] : ((r1_xboole_0(X1,k3_subset_1(X0,X2)) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,k3_subset_1(X0,X2)) <=> r1_tarski(X1,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f45])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    spl3_1 | spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f39,f35])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ~spl3_1 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f39,f35])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ~r1_tarski(sK1,sK2) | ~r1_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (28445)------------------------------
% 0.21/0.50  % (28445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28445)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (28445)Memory used [KB]: 10618
% 0.21/0.50  % (28445)Time elapsed: 0.085 s
% 0.21/0.50  % (28445)------------------------------
% 0.21/0.50  % (28445)------------------------------
% 0.21/0.50  % (28437)Success in time 0.144 s
%------------------------------------------------------------------------------
