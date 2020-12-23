%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1157+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:23 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 781 expanded)
%              Number of leaves         :   20 ( 257 expanded)
%              Depth                    :   25
%              Number of atoms          :  783 (6918 expanded)
%              Number of equality atoms :   70 ( 180 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f689,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f86,f101,f113,f124,f627,f644,f688])).

% (3514)Refutation not found, incomplete strategy% (3514)------------------------------
% (3514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3514)Termination reason: Refutation not found, incomplete strategy

% (3514)Memory used [KB]: 1663
% (3514)Time elapsed: 0.105 s
% (3514)------------------------------
% (3514)------------------------------
fof(f688,plain,
    ( ~ spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(avatar_contradiction_clause,[],[f687])).

fof(f687,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f686,f642])).

fof(f642,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f84,f100])).

fof(f100,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_4
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f84,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_2
  <=> r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f686,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f685,f182])).

fof(f182,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f181,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ r2_orders_2(sK0,sK1,sK2) )
    & ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | r2_orders_2(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | r2_orders_2(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
                | ~ r2_orders_2(sK0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
                | r2_orders_2(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
              | ~ r2_orders_2(sK0,X1,X2) )
            & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
              | r2_orders_2(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
            | ~ r2_orders_2(sK0,sK1,X2) )
          & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
            | r2_orders_2(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
          | ~ r2_orders_2(sK0,sK1,X2) )
        & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
          | r2_orders_2(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ r2_orders_2(sK0,sK1,sK2) )
      & ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | r2_orders_2(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_orders_2(X0,X1,X2)
                <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).

fof(f181,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f180,f45])).

fof(f45,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f180,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f179,f46])).

fof(f46,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f179,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f178,f47])).

fof(f47,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f178,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f174,f48])).

fof(f48,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f174,plain,
    ( k1_orders_2(sK0,k1_tarski(sK1)) = a_2_0_orders_2(sK0,k1_tarski(sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(resolution,[],[f125,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(f125,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f123,f100])).

fof(f123,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_7
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f685,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f684,f44])).

fof(f684,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f683,f45])).

fof(f683,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f682,f46])).

fof(f682,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f681,f47])).

fof(f681,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f680,f48])).

fof(f680,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f679,f125])).

fof(f679,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f678,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f678,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_1
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f677,f79])).

fof(f79,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_1
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f677,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_23 ),
    inference(superposition,[],[f74,f669])).

fof(f669,plain,
    ( sK1 = sK4(sK0,k1_tarski(sK1),sK2)
    | ~ spl6_23 ),
    inference(resolution,[],[f640,f73])).

fof(f73,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f640,plain,
    ( r2_hidden(sK4(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f638])).

fof(f638,plain,
    ( spl6_23
  <=> r2_hidden(sK4(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f74,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
                & r2_hidden(sK4(X1,X2,X3),X2)
                & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK5(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK5(X0,X1,X2) = X0
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f42,f41])).

fof(f41,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
        & r2_hidden(sK4(X1,X2,X3),X2)
        & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK5(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK5(X0,X1,X2) = X0
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

% (3507)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f644,plain,
    ( spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f643])).

fof(f643,plain,
    ( $false
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | spl6_23 ),
    inference(global_subsumption,[],[f245,f642,f639])).

% (3515)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f639,plain,
    ( ~ r2_hidden(sK4(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f638])).

fof(f245,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | r2_hidden(sK4(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f242,f182])).

fof(f242,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | r2_hidden(sK4(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1))
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(resolution,[],[f155,f125])).

fof(f155,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | r2_hidden(sK4(sK0,X1,sK2),X1) ) ),
    inference(subsumption_resolution,[],[f154,f44])).

fof(f154,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK2),X1)
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f45])).

fof(f153,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK2),X1)
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f46])).

fof(f152,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK2),X1)
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f151,f47])).

fof(f151,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK2),X1)
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f48])).

fof(f145,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK0,X1,sK2),X1)
      | r2_hidden(sK2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f75,f50])).

fof(f75,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(sK4(X1,X2,X3),X2)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK4(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f627,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f626])).

fof(f626,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f625,f80])).

fof(f80,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f625,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f623,f620])).

fof(f620,plain,
    ( sK2 = sK5(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(resolution,[],[f472,f208])).

fof(f208,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(superposition,[],[f83,f100])).

fof(f83,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f472,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2 )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f471,f44])).

fof(f471,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f470,f45])).

fof(f470,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f469,f46])).

fof(f469,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f468,f47])).

fof(f468,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f467,f48])).

fof(f467,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f453,f125])).

fof(f453,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_orders_2(sK0,k1_tarski(sK1)))
        | sK5(X2,sK0,k1_tarski(sK1)) = X2
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(superposition,[],[f65,f182])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | sK5(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f623,plain,
    ( r2_orders_2(sK0,sK1,sK5(sK2,sK0,k1_tarski(sK1)))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(resolution,[],[f460,f208])).

fof(f460,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1))) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f459,f44])).

fof(f459,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f458,f45])).

fof(f458,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f457,f46])).

fof(f457,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f456,f47])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f455,f48])).

fof(f455,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f454,f125])).

fof(f454,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f451,f49])).

fof(f49,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f451,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | r2_orders_2(sK0,sK1,sK5(X0,sK0,k1_tarski(sK1)))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(superposition,[],[f169,f182])).

fof(f169,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X4,a_2_0_orders_2(X2,k1_tarski(X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | r2_orders_2(X2,X3,sK5(X4,X2,k1_tarski(X3)))
      | ~ m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_orders_2(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f66,f72])).

fof(f72,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ r2_hidden(X6,X2)
      | r2_orders_2(X1,X6,sK5(X0,X1,X2))
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f124,plain,
    ( spl6_3
    | spl6_7 ),
    inference(avatar_split_clause,[],[f107,f121,f94])).

fof(f94,plain,
    ( spl6_3
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f107,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f49])).

% (3522)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f113,plain,(
    ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f111,f44])).

fof(f111,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f109,f88])).

fof(f88,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f54,f48])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f109,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f96,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f96,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f101,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f91,f98,f94])).

fof(f91,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f58,f49])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f86,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f51,f82,f78])).

fof(f51,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f52,f82,f78])).

fof(f52,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

%------------------------------------------------------------------------------
