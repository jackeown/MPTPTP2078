%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0364+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  99 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :  156 ( 270 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f36,f37,f45,f51,f56,f66,f69,f79])).

fof(f79,plain,
    ( ~ spl3_2
    | spl3_4
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | ~ spl3_2
    | spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f77,f26])).

fof(f26,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f77,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f72,f35])).

fof(f35,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_4
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_8 ),
    inference(superposition,[],[f65,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f65,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl3_8
  <=> r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f69,plain,
    ( ~ spl3_2
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | ~ spl3_2
    | spl3_7 ),
    inference(subsumption_resolution,[],[f67,f26])).

fof(f67,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl3_7 ),
    inference(resolution,[],[f61,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f61,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_7
  <=> m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f66,plain,
    ( ~ spl3_7
    | spl3_8
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f57,f54,f19,f63,f59])).

fof(f19,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f54,plain,
    ( spl3_6
  <=> ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(X0))
        | r1_tarski(sK1,k3_subset_1(X0,k3_subset_1(sK0,sK2)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f57,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,k3_subset_1(sK0,sK2)))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f55,f21])).

fof(f21,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f55,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | r1_tarski(sK1,k3_subset_1(X0,k3_subset_1(sK0,sK2)))
        | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(X0)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f54])).

fof(f56,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f52,f29,f54])).

fof(f29,plain,
    ( spl3_3
  <=> r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(X0))
        | r1_tarski(sK1,k3_subset_1(X0,k3_subset_1(sK0,sK2)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f30,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f30,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f51,plain,
    ( spl3_3
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f50,f43,f24,f19,f29])).

fof(f43,plain,
    ( spl3_5
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | r1_xboole_0(sK1,k3_subset_1(X0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f50,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f46,f21])).

fof(f46,plain,
    ( r1_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f44,f26])).

fof(f44,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | r1_xboole_0(sK1,k3_subset_1(X0,sK2))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0)) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f45,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f41,f33,f43])).

fof(f41,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | r1_xboole_0(sK1,k3_subset_1(X0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(X0)) )
    | ~ spl3_4 ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f33])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_xboole_0(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f39,f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_xboole_0(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f16,f15])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f10,f33,f29])).

fof(f10,plain,
    ( r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f36,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f11,f33,f29])).

fof(f11,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f27,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f12,f24])).

fof(f12,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f19])).

fof(f13,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
