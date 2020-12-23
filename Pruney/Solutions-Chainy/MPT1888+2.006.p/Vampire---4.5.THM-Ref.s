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
% DateTime   : Thu Dec  3 13:22:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 625 expanded)
%              Number of leaves         :   26 ( 218 expanded)
%              Depth                    :   25
%              Number of atoms          :  648 (3597 expanded)
%              Number of equality atoms :   88 ( 590 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f780,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f123,f127,f359,f363,f770])).

fof(f770,plain,
    ( spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_contradiction_clause,[],[f769])).

fof(f769,plain,
    ( $false
    | spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f768,f154])).

fof(f154,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | spl7_2 ),
    inference(forward_demodulation,[],[f150,f149])).

fof(f149,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f145,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl7_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f145,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f94,f65])).

fof(f65,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
              & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
            & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
          & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
      & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f86,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f150,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | spl7_2 ),
    inference(backward_demodulation,[],[f67,f148])).

fof(f148,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f144,f116])).

fof(f144,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f768,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f767,f149])).

fof(f767,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f760,f65])).

fof(f760,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(resolution,[],[f759,f263])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f262,f60])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f262,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f261,f61])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f261,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f260,f62])).

fof(f62,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f259,f63])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(subsumption_resolution,[],[f257,f64])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
        | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl7_2 ),
    inference(superposition,[],[f73,f148])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

fof(f759,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f758,f741])).

fof(f741,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f740,f122])).

fof(f122,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl7_3
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f740,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ r2_hidden(sK2,u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f739,f61])).

fof(f739,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK2,u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f738,f63])).

fof(f738,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK2,u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f737,f347])).

fof(f347,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl7_10
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f737,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK2,u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f733,f376])).

fof(f376,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f375,f61])).

fof(f375,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f374,f63])).

fof(f374,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f373,f62])).

fof(f373,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f365,f352])).

fof(f352,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl7_11
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f365,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_10 ),
    inference(resolution,[],[f347,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X2,X0)
      | v3_pre_topc(X2,X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f733,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | ~ v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ r2_hidden(sK2,u1_struct_0(sK0))
    | spl7_2 ),
    inference(resolution,[],[f230,f157])).

fof(f157,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl7_2 ),
    inference(forward_demodulation,[],[f152,f149])).

fof(f152,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl7_2 ),
    inference(backward_demodulation,[],[f66,f148])).

fof(f66,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_pre_topc(X1,k2_tarski(X2,X2)))
      | ~ r1_xboole_0(X0,k2_tarski(X2,X2))
      | ~ v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ r2_hidden(X2,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f78,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f84,f68])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X1,X0)
                  & r1_xboole_0(X1,X2) )
               => r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).

fof(f758,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(superposition,[],[f81,f742])).

fof(f742,plain,
    ( sK2 = sK5(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2))
    | spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(resolution,[],[f741,f132])).

fof(f132,plain,(
    ! [X4,X5] :
      ( r1_xboole_0(X5,k2_tarski(X4,X4))
      | sK5(X5,k2_tarski(X4,X4)) = X4 ) ),
    inference(resolution,[],[f101,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f101,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f89,f68])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f363,plain,
    ( ~ spl7_10
    | spl7_11
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f362,f111,f350,f346])).

fof(f111,plain,
    ( spl7_1
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f362,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f361,f63])).

fof(f361,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f360,f61])).

fof(f360,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f356,f100])).

fof(f100,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f90,f68])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f356,plain,
    ( ~ r2_hidden(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK1,sK1))))
    | v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(superposition,[],[f200,f336])).

fof(f336,plain,
    ( k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f329,f63])).

fof(f329,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | ~ spl7_1 ),
    inference(resolution,[],[f177,f113])).

fof(f113,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k2_tarski(X1,X1)) = k2_pre_topc(X0,k2_pre_topc(X0,k2_tarski(X1,X1))) ) ),
    inference(resolution,[],[f88,f93])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f200,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k2_pre_topc(X2,X3),k2_tarski(X3,X3))
      | v4_pre_topc(X3,X2)
      | ~ v2_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(extensionality_resolution,[],[f101,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f359,plain,
    ( ~ spl7_1
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl7_1
    | spl7_10 ),
    inference(subsumption_resolution,[],[f357,f113])).

fof(f357,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | spl7_10 ),
    inference(resolution,[],[f355,f93])).

fof(f355,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_10 ),
    inference(subsumption_resolution,[],[f354,f63])).

fof(f354,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl7_10 ),
    inference(resolution,[],[f348,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f348,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f346])).

fof(f127,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f125,f60])).

fof(f125,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f124,f103])).

fof(f103,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f69,f63])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f124,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f117,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f117,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f115])).

% (21706)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
fof(f123,plain,
    ( spl7_3
    | spl7_2 ),
    inference(avatar_split_clause,[],[f109,f115,f120])).

fof(f109,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f85,f65])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f118,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f108,f115,f111])).

fof(f108,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f85,f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n014.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 09:23:07 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.42  % (21702)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.46  % (21696)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (21704)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.47  % (21704)Refutation not found, incomplete strategy% (21704)------------------------------
% 0.20/0.47  % (21704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21704)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (21704)Memory used [KB]: 1791
% 0.20/0.47  % (21704)Time elapsed: 0.079 s
% 0.20/0.47  % (21704)------------------------------
% 0.20/0.47  % (21704)------------------------------
% 0.20/0.48  % (21713)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.49  % (21694)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.49  % (21697)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.49  % (21695)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (21698)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (21693)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (21696)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f780,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f118,f123,f127,f359,f363,f770])).
% 0.20/0.50  fof(f770,plain,(
% 0.20/0.50    spl7_2 | ~spl7_3 | ~spl7_10 | ~spl7_11),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f769])).
% 0.20/0.50  fof(f769,plain,(
% 0.20/0.50    $false | (spl7_2 | ~spl7_3 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f768,f154])).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) != k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | spl7_2),
% 0.20/0.50    inference(forward_demodulation,[],[f150,f149])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | spl7_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f145,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ~v1_xboole_0(u1_struct_0(sK0)) | spl7_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f115])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    spl7_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f94,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ((k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f44,f43,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) => (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f16])).
% 0.20/0.50  fof(f16,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f86,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.50    inference(flattening,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) != k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | spl7_2),
% 0.20/0.50    inference(backward_demodulation,[],[f67,f148])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | spl7_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f144,f116])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f94,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f768,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_tarski(sK2,sK2)) | (spl7_2 | ~spl7_3 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f767,f149])).
% 0.20/0.50  fof(f767,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | (spl7_2 | ~spl7_3 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f760,f65])).
% 0.20/0.50  fof(f760,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k2_tarski(sK1,sK1)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (spl7_2 | ~spl7_3 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(resolution,[],[f759,f263])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | spl7_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f262,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | spl7_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f261,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    v2_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl7_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f260,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    v3_tdlat_3(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl7_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f259,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl7_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f257,f64])).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | spl7_2),
% 0.20/0.50    inference(superposition,[],[f73,f148])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).
% 0.20/0.50  fof(f759,plain,(
% 0.20/0.50    r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | (spl7_2 | ~spl7_3 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f758,f741])).
% 0.20/0.50  fof(f741,plain,(
% 0.20/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | (spl7_2 | ~spl7_3 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f740,f122])).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl7_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f120])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    spl7_3 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.50  fof(f740,plain,(
% 0.20/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | ~r2_hidden(sK2,u1_struct_0(sK0)) | (spl7_2 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f739,f61])).
% 0.20/0.50  fof(f739,plain,(
% 0.20/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | ~v2_pre_topc(sK0) | ~r2_hidden(sK2,u1_struct_0(sK0)) | (spl7_2 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f738,f63])).
% 0.20/0.50  fof(f738,plain,(
% 0.20/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~r2_hidden(sK2,u1_struct_0(sK0)) | (spl7_2 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f737,f347])).
% 0.20/0.50  fof(f347,plain,(
% 0.20/0.50    m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f346])).
% 0.20/0.50  fof(f346,plain,(
% 0.20/0.50    spl7_10 <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.50  fof(f737,plain,(
% 0.20/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~r2_hidden(sK2,u1_struct_0(sK0)) | (spl7_2 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f733,f376])).
% 0.20/0.50  fof(f376,plain,(
% 0.20/0.50    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | (~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f375,f61])).
% 0.20/0.50  fof(f375,plain,(
% 0.20/0.50    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~v2_pre_topc(sK0) | (~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f374,f63])).
% 0.20/0.50  fof(f374,plain,(
% 0.20/0.50    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f373,f62])).
% 0.20/0.50  fof(f373,plain,(
% 0.20/0.50    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f365,f352])).
% 0.20/0.50  fof(f352,plain,(
% 0.20/0.50    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~spl7_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f350])).
% 0.20/0.50  fof(f350,plain,(
% 0.20/0.50    spl7_11 <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.50  fof(f365,plain,(
% 0.20/0.50    ~v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl7_10),
% 0.20/0.50    inference(resolution,[],[f347,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X2,X0) | v3_pre_topc(X2,X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(rectify,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.20/0.50  fof(f733,plain,(
% 0.20/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | ~v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~r2_hidden(sK2,u1_struct_0(sK0)) | spl7_2),
% 0.20/0.50    inference(resolution,[],[f230,f157])).
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl7_2),
% 0.20/0.50    inference(forward_demodulation,[],[f152,f149])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl7_2),
% 0.20/0.50    inference(backward_demodulation,[],[f66,f148])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f230,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_pre_topc(X1,k2_tarski(X2,X2))) | ~r1_xboole_0(X0,k2_tarski(X2,X2)) | ~v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~r2_hidden(X2,u1_struct_0(X1))) )),
% 0.20/0.50    inference(resolution,[],[f78,f93])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f84,f68])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).
% 0.20/0.50  fof(f758,plain,(
% 0.20/0.50    r2_hidden(sK2,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | (spl7_2 | ~spl7_3 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(superposition,[],[f81,f742])).
% 0.20/0.50  fof(f742,plain,(
% 0.20/0.50    sK2 = sK5(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(sK2,sK2)) | (spl7_2 | ~spl7_3 | ~spl7_10 | ~spl7_11)),
% 0.20/0.50    inference(resolution,[],[f741,f132])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X4,X5] : (r1_xboole_0(X5,k2_tarski(X4,X4)) | sK5(X5,k2_tarski(X4,X4)) = X4) )),
% 0.20/0.50    inference(resolution,[],[f101,f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.20/0.50    inference(equality_resolution,[],[f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.20/0.50    inference(definition_unfolding,[],[f89,f68])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f57,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK6(X0,X1) != X0 | ~r2_hidden(sK6(X0,X1),X1)) & (sK6(X0,X1) = X0 | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.50    inference(rectify,[],[f56])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f55])).
% 0.20/0.50  fof(f363,plain,(
% 0.20/0.50    ~spl7_10 | spl7_11 | ~spl7_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f362,f111,f350,f346])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    spl7_1 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f361,f63])).
% 0.20/0.50  fof(f361,plain,(
% 0.20/0.50    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f360,f61])).
% 0.20/0.50  fof(f360,plain,(
% 0.20/0.50    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f356,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.20/0.50    inference(equality_resolution,[],[f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.20/0.50    inference(equality_resolution,[],[f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.20/0.50    inference(definition_unfolding,[],[f90,f68])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f59])).
% 0.20/0.50  fof(f356,plain,(
% 0.20/0.50    ~r2_hidden(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_tarski(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))) | v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.20/0.50    inference(superposition,[],[f200,f336])).
% 0.20/0.50  fof(f336,plain,(
% 0.20/0.50    k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~spl7_1),
% 0.20/0.50    inference(subsumption_resolution,[],[f329,f63])).
% 0.20/0.50  fof(f329,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k2_tarski(sK1,sK1)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | ~spl7_1),
% 0.20/0.50    inference(resolution,[],[f177,f113])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl7_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f111])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k2_tarski(X1,X1)) = k2_pre_topc(X0,k2_pre_topc(X0,k2_tarski(X1,X1)))) )),
% 0.20/0.50    inference(resolution,[],[f88,f93])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r2_hidden(k2_pre_topc(X2,X3),k2_tarski(X3,X3)) | v4_pre_topc(X3,X2) | ~v2_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.20/0.50    inference(extensionality_resolution,[],[f101,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.50  fof(f359,plain,(
% 0.20/0.50    ~spl7_1 | spl7_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f358])).
% 0.20/0.50  fof(f358,plain,(
% 0.20/0.50    $false | (~spl7_1 | spl7_10)),
% 0.20/0.50    inference(subsumption_resolution,[],[f357,f113])).
% 0.20/0.50  fof(f357,plain,(
% 0.20/0.50    ~r2_hidden(sK1,u1_struct_0(sK0)) | spl7_10),
% 0.20/0.50    inference(resolution,[],[f355,f93])).
% 0.20/0.50  fof(f355,plain,(
% 0.20/0.50    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl7_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f354,f63])).
% 0.20/0.50  fof(f354,plain,(
% 0.20/0.50    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl7_10),
% 0.20/0.50    inference(resolution,[],[f348,f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.20/0.50  fof(f348,plain,(
% 0.20/0.50    ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl7_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f346])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ~spl7_2),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    $false | ~spl7_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f125,f60])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    v2_struct_0(sK0) | ~spl7_2),
% 0.20/0.50    inference(subsumption_resolution,[],[f124,f103])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    l1_struct_0(sK0)),
% 0.20/0.50    inference(resolution,[],[f69,f63])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl7_2),
% 0.20/0.50    inference(resolution,[],[f117,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    v1_xboole_0(u1_struct_0(sK0)) | ~spl7_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f115])).
% 0.20/0.50  % (21706)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    spl7_3 | spl7_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f109,f115,f120])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK2,u1_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f85,f65])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    spl7_1 | spl7_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f108,f115,f111])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f85,f64])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (21696)------------------------------
% 0.20/0.50  % (21696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21696)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (21696)Memory used [KB]: 11257
% 0.20/0.50  % (21696)Time elapsed: 0.098 s
% 0.20/0.50  % (21696)------------------------------
% 0.20/0.50  % (21696)------------------------------
% 0.20/0.50  % (21703)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.51  % (21689)Success in time 0.157 s
%------------------------------------------------------------------------------
