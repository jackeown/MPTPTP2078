%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 225 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  426 ( 945 expanded)
%              Number of equality atoms :   68 ( 121 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f552,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f275,f280,f283,f536,f551])).

fof(f551,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f550])).

fof(f550,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f163,f305])).

fof(f305,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f216,f54])).

fof(f54,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( v3_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( v3_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v1_xboole_0(X1) )
   => ( v3_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).

fof(f216,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f172,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f172,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f92,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f92,plain,(
    ! [X1] : m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f81,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f163,plain,
    ( k1_xboole_0 != sK1
    | spl4_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f536,plain,
    ( ~ spl4_9
    | spl4_13
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f535])).

fof(f535,plain,
    ( $false
    | ~ spl4_9
    | spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f534,f53])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f534,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_9
    | spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f533,f183])).

fof(f183,plain,
    ( v3_tex_2(k1_xboole_0,sK0)
    | ~ spl4_9 ),
    inference(superposition,[],[f56,f164])).

fof(f164,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f56,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f533,plain,
    ( ~ v3_tex_2(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f532,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f73,f60])).

fof(f60,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f73,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f532,plain,
    ( k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0)))
    | ~ v3_tex_2(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f531,f269])).

fof(f269,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl4_13
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f531,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0)))
    | ~ v3_tex_2(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f530,f290])).

fof(f290,plain,
    ( v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0)
    | spl4_13
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f289,f274])).

fof(f274,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl4_14
  <=> k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f289,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))),sK0)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f288,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f288,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))),sK0)
    | v2_struct_0(sK0)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f287,f269])).

fof(f287,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))),sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f286,f53])).

fof(f286,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))),sK0)
    | ~ l1_pre_topc(sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f201,f52])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f201,plain,(
    ! [X12] :
      ( ~ v2_pre_topc(X12)
      | v2_tex_2(k6_domain_1(u1_struct_0(X12),sK3(u1_struct_0(X12))),X12)
      | ~ l1_pre_topc(X12)
      | k1_xboole_0 = u1_struct_0(X12)
      | v2_struct_0(X12) ) ),
    inference(resolution,[],[f88,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f70,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f530,plain,
    ( ~ v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0)
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0)))
    | ~ v3_tex_2(k1_xboole_0,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_14 ),
    inference(superposition,[],[f257,f274])).

fof(f257,plain,(
    ! [X5] :
      ( ~ v2_tex_2(k6_domain_1(u1_struct_0(X5),sK3(u1_struct_0(X5))),X5)
      | k1_xboole_0 = u1_struct_0(X5)
      | k1_xboole_0 = k6_domain_1(u1_struct_0(X5),sK3(u1_struct_0(X5)))
      | ~ v3_tex_2(k1_xboole_0,X5)
      | ~ l1_pre_topc(X5) ) ),
    inference(subsumption_resolution,[],[f247,f216])).

fof(f247,plain,(
    ! [X5] :
      ( k1_xboole_0 = u1_struct_0(X5)
      | v1_xboole_0(u1_struct_0(X5))
      | ~ v2_tex_2(k6_domain_1(u1_struct_0(X5),sK3(u1_struct_0(X5))),X5)
      | k1_xboole_0 = k6_domain_1(u1_struct_0(X5),sK3(u1_struct_0(X5)))
      | ~ v3_tex_2(k1_xboole_0,X5)
      | ~ l1_pre_topc(X5) ) ),
    inference(resolution,[],[f199,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_tex_2(X0,X1)
      | k1_xboole_0 = X0
      | ~ v3_tex_2(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f154,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f154,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v2_tex_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_tex_2(k1_xboole_0,X1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f63,f58])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X1,X3)
      | X1 = X3
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f199,plain,(
    ! [X10] :
      ( m1_subset_1(k6_domain_1(X10,sK3(X10)),k1_zfmisc_1(X10))
      | k1_xboole_0 = X10
      | v1_xboole_0(X10) ) ),
    inference(resolution,[],[f88,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f283,plain,
    ( spl4_4
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f281,f57])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f281,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_4
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f114,f270])).

fof(f270,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f268])).

fof(f114,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f280,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f278,f51])).

fof(f278,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f277,f86])).

fof(f86,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f61,f53])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f277,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f113,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f113,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f275,plain,
    ( spl4_13
    | spl4_14
    | spl4_4 ),
    inference(avatar_split_clause,[],[f266,f112,f272,f268])).

fof(f266,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0)))
    | k1_xboole_0 = u1_struct_0(sK0)
    | spl4_4 ),
    inference(resolution,[],[f200,f114])).

fof(f200,plain,(
    ! [X11] :
      ( v1_xboole_0(X11)
      | k6_domain_1(X11,sK3(X11)) = k1_tarski(sK3(X11))
      | k1_xboole_0 = X11 ) ),
    inference(resolution,[],[f88,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:00:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (5882)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.48  % (5891)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.49  % (5882)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (5887)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (5878)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f552,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f275,f280,f283,f536,f551])).
% 0.22/0.51  fof(f551,plain,(
% 0.22/0.51    spl4_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f550])).
% 0.22/0.51  fof(f550,plain,(
% 0.22/0.51    $false | spl4_9),
% 0.22/0.51    inference(subsumption_resolution,[],[f163,f305])).
% 0.22/0.51  fof(f305,plain,(
% 0.22/0.51    k1_xboole_0 = sK1),
% 0.22/0.51    inference(resolution,[],[f216,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    v1_xboole_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    (v3_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f39,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ? [X1] : (v3_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(X1)) => (v3_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v1_xboole_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.22/0.51    inference(negated_conjecture,[],[f18])).
% 0.22/0.51  fof(f18,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tex_2)).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(resolution,[],[f172,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~r2_hidden(X3,X2) | ~v1_xboole_0(X2)) )),
% 0.22/0.51    inference(resolution,[],[f92,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(resolution,[],[f81,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    k1_xboole_0 != sK1 | spl4_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f162])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    spl4_9 <=> k1_xboole_0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.51  fof(f536,plain,(
% 0.22/0.51    ~spl4_9 | spl4_13 | ~spl4_14),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f535])).
% 0.22/0.51  fof(f535,plain,(
% 0.22/0.51    $false | (~spl4_9 | spl4_13 | ~spl4_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f534,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f534,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | (~spl4_9 | spl4_13 | ~spl4_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f533,f183])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    v3_tex_2(k1_xboole_0,sK0) | ~spl4_9),
% 0.22/0.51    inference(superposition,[],[f56,f164])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    k1_xboole_0 = sK1 | ~spl4_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f162])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    v3_tex_2(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f533,plain,(
% 0.22/0.51    ~v3_tex_2(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | (spl4_13 | ~spl4_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f532,f87])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.22/0.51    inference(superposition,[],[f73,f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.22/0.51  fof(f532,plain,(
% 0.22/0.51    k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0))) | ~v3_tex_2(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | (spl4_13 | ~spl4_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f531,f269])).
% 0.22/0.51  fof(f269,plain,(
% 0.22/0.51    k1_xboole_0 != u1_struct_0(sK0) | spl4_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f268])).
% 0.22/0.51  fof(f268,plain,(
% 0.22/0.51    spl4_13 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.51  fof(f531,plain,(
% 0.22/0.51    k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0))) | ~v3_tex_2(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | (spl4_13 | ~spl4_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f530,f290])).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0) | (spl4_13 | ~spl4_14)),
% 0.22/0.51    inference(forward_demodulation,[],[f289,f274])).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0))) | ~spl4_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f272])).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    spl4_14 <=> k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))),sK0) | spl4_13),
% 0.22/0.51    inference(subsumption_resolution,[],[f288,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))),sK0) | v2_struct_0(sK0) | spl4_13),
% 0.22/0.51    inference(subsumption_resolution,[],[f287,f269])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))),sK0) | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f286,f53])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))),sK0) | ~l1_pre_topc(sK0) | k1_xboole_0 = u1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f201,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ( ! [X12] : (~v2_pre_topc(X12) | v2_tex_2(k6_domain_1(u1_struct_0(X12),sK3(u1_struct_0(X12))),X12) | ~l1_pre_topc(X12) | k1_xboole_0 = u1_struct_0(X12) | v2_struct_0(X12)) )),
% 0.22/0.51    inference(resolution,[],[f88,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(resolution,[],[f70,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.51  fof(f530,plain,(
% 0.22/0.51    ~v2_tex_2(k1_tarski(sK3(u1_struct_0(sK0))),sK0) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = k1_tarski(sK3(u1_struct_0(sK0))) | ~v3_tex_2(k1_xboole_0,sK0) | ~l1_pre_topc(sK0) | ~spl4_14),
% 0.22/0.51    inference(superposition,[],[f257,f274])).
% 0.22/0.51  fof(f257,plain,(
% 0.22/0.51    ( ! [X5] : (~v2_tex_2(k6_domain_1(u1_struct_0(X5),sK3(u1_struct_0(X5))),X5) | k1_xboole_0 = u1_struct_0(X5) | k1_xboole_0 = k6_domain_1(u1_struct_0(X5),sK3(u1_struct_0(X5))) | ~v3_tex_2(k1_xboole_0,X5) | ~l1_pre_topc(X5)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f247,f216])).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    ( ! [X5] : (k1_xboole_0 = u1_struct_0(X5) | v1_xboole_0(u1_struct_0(X5)) | ~v2_tex_2(k6_domain_1(u1_struct_0(X5),sK3(u1_struct_0(X5))),X5) | k1_xboole_0 = k6_domain_1(u1_struct_0(X5),sK3(u1_struct_0(X5))) | ~v3_tex_2(k1_xboole_0,X5) | ~l1_pre_topc(X5)) )),
% 0.22/0.51    inference(resolution,[],[f199,f158])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_tex_2(X0,X1) | k1_xboole_0 = X0 | ~v3_tex_2(k1_xboole_0,X1) | ~l1_pre_topc(X1)) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f154,f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~v2_tex_2(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_tex_2(k1_xboole_0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 0.22/0.51    inference(resolution,[],[f63,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r1_tarski(X1,X3) | X1 = X3 | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(rectify,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    ( ! [X10] : (m1_subset_1(k6_domain_1(X10,sK3(X10)),k1_zfmisc_1(X10)) | k1_xboole_0 = X10 | v1_xboole_0(X10)) )),
% 0.22/0.51    inference(resolution,[],[f88,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    spl4_4 | ~spl4_13),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f282])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    $false | (spl4_4 | ~spl4_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f281,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    v1_xboole_0(k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.51  fof(f281,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_xboole_0) | (spl4_4 | ~spl4_13)),
% 0.22/0.51    inference(forward_demodulation,[],[f114,f270])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    k1_xboole_0 = u1_struct_0(sK0) | ~spl4_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f268])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f112])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    spl4_4 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    ~spl4_4),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f279])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    $false | ~spl4_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f278,f51])).
% 0.22/0.51  fof(f278,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~spl4_4),
% 0.22/0.51    inference(subsumption_resolution,[],[f277,f86])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    l1_struct_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f61,f53])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl4_4),
% 0.22/0.51    inference(resolution,[],[f113,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f112])).
% 0.22/0.51  fof(f275,plain,(
% 0.22/0.51    spl4_13 | spl4_14 | spl4_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f266,f112,f272,f268])).
% 0.22/0.51  fof(f266,plain,(
% 0.22/0.51    k6_domain_1(u1_struct_0(sK0),sK3(u1_struct_0(sK0))) = k1_tarski(sK3(u1_struct_0(sK0))) | k1_xboole_0 = u1_struct_0(sK0) | spl4_4),
% 0.22/0.51    inference(resolution,[],[f200,f114])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ( ! [X11] : (v1_xboole_0(X11) | k6_domain_1(X11,sK3(X11)) = k1_tarski(sK3(X11)) | k1_xboole_0 = X11) )),
% 0.22/0.51    inference(resolution,[],[f88,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (5882)------------------------------
% 0.22/0.51  % (5882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (5882)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (5882)Memory used [KB]: 11001
% 0.22/0.51  % (5882)Time elapsed: 0.069 s
% 0.22/0.51  % (5882)------------------------------
% 0.22/0.51  % (5882)------------------------------
% 0.22/0.51  % (5871)Success in time 0.145 s
%------------------------------------------------------------------------------
