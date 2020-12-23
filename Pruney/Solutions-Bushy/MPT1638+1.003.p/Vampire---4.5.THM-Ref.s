%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1638+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 941 expanded)
%              Number of leaves         :   18 ( 293 expanded)
%              Depth                    :   24
%              Number of atoms          :  527 (5991 expanded)
%              Number of equality atoms :   71 ( 242 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f465,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f87,f111,f223,f464])).

fof(f464,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | spl6_4 ),
    inference(subsumption_resolution,[],[f462,f85])).

fof(f85,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_2
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f462,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_1
    | spl6_4 ),
    inference(forward_demodulation,[],[f461,f452])).

fof(f452,plain,
    ( sK1 = sK5(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_1
    | spl6_4 ),
    inference(resolution,[],[f446,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f446,plain,
    ( r2_hidden(sK5(sK2,sK0,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl6_1
    | spl6_4 ),
    inference(resolution,[],[f317,f80])).

fof(f80,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_1
  <=> r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f317,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k6_waybel_0(sK0,sK1))
        | r2_hidden(sK5(X3,sK0,k1_tarski(sK1)),k1_tarski(sK1)) )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f316,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_orders_2(sK0,sK1,sK2)
      | ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )
    & ( r1_orders_2(sK0,sK1,sK2)
      | r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
                & ( r1_orders_2(X0,X1,X2)
                  | r2_hidden(X2,k6_waybel_0(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(sK0,X1)) )
              & ( r1_orders_2(sK0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_orders_2(sK0,X1,X2)
              | ~ r2_hidden(X2,k6_waybel_0(sK0,X1)) )
            & ( r1_orders_2(sK0,X1,X2)
              | r2_hidden(X2,k6_waybel_0(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r1_orders_2(sK0,sK1,X2)
            | ~ r2_hidden(X2,k6_waybel_0(sK0,sK1)) )
          & ( r1_orders_2(sK0,sK1,X2)
            | r2_hidden(X2,k6_waybel_0(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( ~ r1_orders_2(sK0,sK1,X2)
          | ~ r2_hidden(X2,k6_waybel_0(sK0,sK1)) )
        & ( r1_orders_2(sK0,sK1,X2)
          | r2_hidden(X2,k6_waybel_0(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r1_orders_2(sK0,sK1,sK2)
        | ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )
      & ( r1_orders_2(sK0,sK1,sK2)
        | r2_hidden(sK2,k6_waybel_0(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k6_waybel_0(X0,X1))
                <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

fof(f316,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k6_waybel_0(sK0,sK1))
        | r2_hidden(sK5(X3,sK0,k1_tarski(sK1)),k1_tarski(sK1))
        | v2_struct_0(sK0) )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f315,f50])).

fof(f50,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f315,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k6_waybel_0(sK0,sK1))
        | r2_hidden(sK5(X3,sK0,k1_tarski(sK1)),k1_tarski(sK1))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f304,f119])).

fof(f119,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_4 ),
    inference(forward_demodulation,[],[f118,f114])).

fof(f114,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f112,f100])).

fof(f100,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f112,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f60,f51])).

fof(f51,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f118,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f116,f100])).

fof(f116,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f61,f51])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f304,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k6_waybel_0(sK0,sK1))
        | r2_hidden(sK5(X3,sK0,k1_tarski(sK1)),k1_tarski(sK1))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl6_4 ),
    inference(superposition,[],[f71,f172])).

fof(f172,plain,
    ( k6_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,k1_tarski(sK1))
    | spl6_4 ),
    inference(forward_demodulation,[],[f171,f130])).

fof(f130,plain,
    ( k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k1_tarski(sK1))
    | spl6_4 ),
    inference(forward_demodulation,[],[f129,f114])).

fof(f129,plain,(
    k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f128,f49])).

fof(f128,plain,
    ( k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f50])).

fof(f126,plain,
    ( k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f57,f51])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_waybel_0)).

fof(f171,plain,
    ( k4_waybel_0(sK0,k1_tarski(sK1)) = a_2_1_waybel_0(sK0,k1_tarski(sK1))
    | spl6_4 ),
    inference(subsumption_resolution,[],[f170,f49])).

fof(f170,plain,
    ( k4_waybel_0(sK0,k1_tarski(sK1)) = a_2_1_waybel_0(sK0,k1_tarski(sK1))
    | v2_struct_0(sK0)
    | spl6_4 ),
    inference(subsumption_resolution,[],[f165,f50])).

fof(f165,plain,
    ( k4_waybel_0(sK0,k1_tarski(sK1)) = a_2_1_waybel_0(sK0,k1_tarski(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl6_4 ),
    inference(resolution,[],[f119,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_waybel_0)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK5(X0,X1,X2),X2)
            & r1_orders_2(X1,sK5(X0,X1,X2),sK4(X0,X1,X2))
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f45,f47,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r1_orders_2(X1,X6,X5)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r1_orders_2(X1,X6,sK4(X0,X1,X2))
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r1_orders_2(X1,X6,sK4(X0,X1,X2))
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK5(X0,X1,X2),X2)
        & r1_orders_2(X1,sK5(X0,X1,X2),sK4(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r1_orders_2(X1,X6,X5)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r1_orders_2(X1,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_waybel_0)).

fof(f461,plain,
    ( r1_orders_2(sK0,sK5(sK2,sK0,k1_tarski(sK1)),sK2)
    | ~ spl6_1
    | spl6_4 ),
    inference(forward_demodulation,[],[f459,f353])).

fof(f353,plain,
    ( sK2 = sK4(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_1
    | spl6_4 ),
    inference(resolution,[],[f320,f80])).

fof(f320,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k6_waybel_0(sK0,sK1))
        | sK4(X4,sK0,k1_tarski(sK1)) = X4 )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f319,f49])).

fof(f319,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k6_waybel_0(sK0,sK1))
        | sK4(X4,sK0,k1_tarski(sK1)) = X4
        | v2_struct_0(sK0) )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f318,f50])).

fof(f318,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k6_waybel_0(sK0,sK1))
        | sK4(X4,sK0,k1_tarski(sK1)) = X4
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f305,f119])).

fof(f305,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k6_waybel_0(sK0,sK1))
        | sK4(X4,sK0,k1_tarski(sK1)) = X4
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl6_4 ),
    inference(superposition,[],[f68,f172])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | sK4(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f459,plain,
    ( r1_orders_2(sK0,sK5(sK2,sK0,k1_tarski(sK1)),sK4(sK2,sK0,k1_tarski(sK1)))
    | ~ spl6_1
    | spl6_4 ),
    inference(resolution,[],[f308,f80])).

fof(f308,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,sK5(X0,sK0,k1_tarski(sK1)),sK4(X0,sK0,k1_tarski(sK1))) )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f307,f49])).

fof(f307,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,sK5(X0,sK0,k1_tarski(sK1)),sK4(X0,sK0,k1_tarski(sK1)))
        | v2_struct_0(sK0) )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f306,f50])).

fof(f306,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,sK5(X0,sK0,k1_tarski(sK1)),sK4(X0,sK0,k1_tarski(sK1)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl6_4 ),
    inference(subsumption_resolution,[],[f301,f119])).

fof(f301,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k6_waybel_0(sK0,sK1))
        | r1_orders_2(sK0,sK5(X0,sK0,k1_tarski(sK1)),sK4(X0,sK0,k1_tarski(sK1)))
        | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl6_4 ),
    inference(superposition,[],[f70,f172])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | r1_orders_2(X1,sK5(X0,X1,X2),sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f223,plain,
    ( spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(subsumption_resolution,[],[f221,f81])).

fof(f81,plain,
    ( ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f221,plain,
    ( r2_hidden(sK2,k6_waybel_0(sK0,sK1))
    | ~ spl6_2
    | spl6_4 ),
    inference(forward_demodulation,[],[f220,f172])).

fof(f220,plain,
    ( r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | ~ spl6_2
    | spl6_4 ),
    inference(subsumption_resolution,[],[f219,f49])).

fof(f219,plain,
    ( r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | v2_struct_0(sK0)
    | ~ spl6_2
    | spl6_4 ),
    inference(subsumption_resolution,[],[f218,f50])).

fof(f218,plain,
    ( r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2
    | spl6_4 ),
    inference(subsumption_resolution,[],[f217,f119])).

fof(f217,plain,
    ( r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f216,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f216,plain,
    ( r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f215,f51])).

fof(f215,plain,
    ( r2_hidden(sK2,a_2_1_waybel_0(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f150,f84])).

fof(f84,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X2,X0)
      | r2_hidden(X0,a_2_1_waybel_0(X1,k1_tarski(X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X3,a_2_1_waybel_0(X1,X2))
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f111,plain,(
    ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f109,f49])).

fof(f109,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f108,f89])).

fof(f89,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f55,f50])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f108,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f101,f56])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f101,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f87,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f53,f83,f79])).

fof(f53,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f54,f83,f79])).

fof(f54,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k6_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f39])).

%------------------------------------------------------------------------------
