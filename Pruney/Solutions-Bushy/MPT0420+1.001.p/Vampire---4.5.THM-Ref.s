%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0420+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  83 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 239 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f27,f40,f48])).

fof(f48,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f47])).

fof(f47,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f46,f13])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <~> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),X2)
            <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).

fof(f46,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1
    | spl3_2 ),
    inference(resolution,[],[f45,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f45,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f44,f14])).

fof(f14,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f44,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f43,f21])).

fof(f21,plain,
    ( r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl3_1
  <=> r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f43,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f41,f28])).

fof(f28,plain,(
    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) ),
    inference(resolution,[],[f15,f13])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f41,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_setfam_1(X0,sK1),k7_setfam_1(X0,k7_setfam_1(sK0,sK2)))
        | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | spl3_2 ),
    inference(resolution,[],[f24,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f24,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl3_2
  <=> r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f40,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f38,f14])).

fof(f38,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f37,f16])).

fof(f37,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f36,f13])).

fof(f36,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f35,f25])).

fof(f25,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f35,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_1 ),
    inference(superposition,[],[f33,f29])).

fof(f29,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f15,f14])).

fof(f33,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_setfam_1(X0,k7_setfam_1(sK0,sK1)),k7_setfam_1(X0,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | spl3_1 ),
    inference(resolution,[],[f17,f20])).

fof(f20,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f27,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f12,f23,f19])).

fof(f12,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f26,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f11,f23,f19])).

fof(f11,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
