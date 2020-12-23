%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:44 EST 2020

% Result     : Theorem 3.15s
% Output     : Refutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  178 (1356 expanded)
%              Number of leaves         :   24 ( 362 expanded)
%              Depth                    :   23
%              Number of atoms          :  421 (6566 expanded)
%              Number of equality atoms :  105 (1795 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4664,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f149,f4466,f4498,f4592,f4656])).

fof(f4656,plain,
    ( ~ spl2_2
    | ~ spl2_8 ),
    inference(avatar_contradiction_clause,[],[f4655])).

fof(f4655,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_8 ),
    inference(subsumption_resolution,[],[f4608,f4598])).

fof(f4598,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(global_subsumption,[],[f52,f81])).

fof(f81,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f52,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f4608,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_8 ),
    inference(superposition,[],[f113,f148])).

fof(f148,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl2_8
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f113,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f112,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f112,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f111,f49])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f111,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f63,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f4592,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f4591])).

fof(f4591,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f4566,f4508])).

fof(f4508,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(superposition,[],[f82,f162])).

fof(f162,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2) = k4_xboole_0(k2_pre_topc(sK0,sK1),X2) ),
    inference(resolution,[],[f115,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f115,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f114,f49])).

fof(f114,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f64,f50])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f82,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f4566,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f820,f4507])).

fof(f4507,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f4145,f4500])).

fof(f4500,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f4499,f49])).

fof(f4499,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f315,f77])).

fof(f77,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f315,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f125,f50])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X0,X1)
      | r1_tarski(X0,k1_tops_1(X1,X0))
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tops_1(X1,X0))
      | ~ v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f57,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f4145,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(superposition,[],[f521,f3721])).

fof(f3721,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f3699,f202])).

fof(f202,plain,(
    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f201,f93])).

fof(f93,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f92,f91])).

fof(f91,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f60,f50])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f92,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f61,f50])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f201,plain,(
    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f179,f91])).

fof(f179,plain,(
    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f90,f60])).

fof(f90,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f59,f50])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f3699,plain,(
    k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(superposition,[],[f1281,f1358])).

fof(f1358,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f1357,f270])).

fof(f270,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f265,f91])).

fof(f265,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f116,f90])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),X0,X0) = X0 ) ),
    inference(resolution,[],[f72,f50])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k4_subset_1)).

fof(f1357,plain,(
    k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f1356,f238])).

fof(f238,plain,(
    ! [X7] : k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,X7)) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X7)) ),
    inference(forward_demodulation,[],[f217,f110])).

fof(f110,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f71,f50])).

fof(f217,plain,(
    ! [X7] : k4_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X7)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X7)) ),
    inference(resolution,[],[f105,f60])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f70,f50])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f1356,plain,(
    k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f1355,f110])).

fof(f1355,plain,(
    k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f1310,f91])).

fof(f1310,plain,(
    k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f205,f50])).

fof(f205,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(u1_struct_0(sK0),sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k4_xboole_0(u1_struct_0(sK0),sK1)) ) ),
    inference(forward_demodulation,[],[f181,f91])).

fof(f181,plain,(
    ! [X0] :
      ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f90,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(f1281,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,X0))) ),
    inference(superposition,[],[f273,f240])).

fof(f240,plain,(
    ! [X8] : k4_xboole_0(sK1,X8) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,X8))) ),
    inference(forward_demodulation,[],[f239,f238])).

fof(f239,plain,(
    ! [X8] : k4_xboole_0(sK1,X8) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X8))) ),
    inference(forward_demodulation,[],[f218,f110])).

fof(f218,plain,(
    ! [X8] : k7_subset_1(u1_struct_0(sK0),sK1,X8) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X8))) ),
    inference(resolution,[],[f105,f61])).

fof(f273,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k3_subset_1(X2,k4_xboole_0(X2,X3)) ),
    inference(resolution,[],[f87,f60])).

fof(f87,plain,(
    ! [X2,X1] : m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f69,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f521,plain,(
    ! [X2] :
      ( ~ r1_tarski(k4_xboole_0(sK1,X2),k1_tops_1(sK0,k4_xboole_0(sK1,X2)))
      | k4_xboole_0(sK1,X2) = k1_tops_1(sK0,k4_xboole_0(sK1,X2)) ) ),
    inference(resolution,[],[f234,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f234,plain,(
    ! [X4] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X4)),k4_xboole_0(sK1,X4)) ),
    inference(forward_demodulation,[],[f233,f110])).

fof(f233,plain,(
    ! [X4] : r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X4)),k7_subset_1(u1_struct_0(sK0),sK1,X4)) ),
    inference(subsumption_resolution,[],[f214,f49])).

fof(f214,plain,(
    ! [X4] :
      ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X4)),k7_subset_1(u1_struct_0(sK0),sK1,X4))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f105,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f820,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f162,f120])).

fof(f120,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f119,f49])).

fof(f119,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f50])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f4498,plain,
    ( spl2_2
    | spl2_7 ),
    inference(avatar_contradiction_clause,[],[f4497])).

fof(f4497,plain,
    ( $false
    | spl2_2
    | spl2_7 ),
    inference(global_subsumption,[],[f51,f4473,f82])).

fof(f4473,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_7 ),
    inference(subsumption_resolution,[],[f4133,f144])).

fof(f144,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl2_7
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f4133,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f397,f3721])).

fof(f397,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k4_xboole_0(sK1,X0),sK0)
      | r1_tarski(k4_xboole_0(sK1,X0),k1_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f396,f49])).

fof(f396,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k4_xboole_0(sK1,X0),sK0)
      | r1_tarski(k4_xboole_0(sK1,X0),k1_tops_1(sK0,sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f378,f50])).

fof(f378,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(k4_xboole_0(sK1,X0),sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k4_xboole_0(sK1,X0),k1_tops_1(sK0,sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f245,f123])).

fof(f123,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v3_pre_topc(k4_xboole_0(X2,X3),X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
      | r1_tarski(k4_xboole_0(X2,X3),k1_tops_1(X4,X2))
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f57,f58])).

fof(f245,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f105,f110])).

fof(f51,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f4466,plain,
    ( ~ spl2_2
    | spl2_8 ),
    inference(avatar_contradiction_clause,[],[f4465])).

fof(f4465,plain,
    ( $false
    | ~ spl2_2
    | spl2_8 ),
    inference(subsumption_resolution,[],[f4464,f147])).

fof(f147,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f4464,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f4463,f2304])).

fof(f2304,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(superposition,[],[f353,f819])).

fof(f819,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f162,f81])).

fof(f353,plain,(
    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f347,f346])).

fof(f346,plain,(
    k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    inference(resolution,[],[f128,f60])).

fof(f128,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f107,f69])).

fof(f107,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f106,f49])).

fof(f106,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f50])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f347,plain,(
    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(resolution,[],[f128,f61])).

fof(f4463,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4453,f4462])).

fof(f4462,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4452,f820])).

fof(f4452,plain,(
    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f2703,f60])).

fof(f2703,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f2553,f69])).

fof(f2553,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f2294,f262])).

fof(f262,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f118,f110])).

fof(f118,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f117,f49])).

fof(f117,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f50])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f2294,plain,(
    ! [X5] : r1_tarski(k4_xboole_0(sK1,X5),k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2281,f351])).

fof(f351,plain,(
    ! [X2] : k4_xboole_0(sK1,X2) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X2) ),
    inference(resolution,[],[f128,f71])).

fof(f2281,plain,(
    ! [X5] : r1_tarski(k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X5),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f350,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f350,plain,(
    ! [X1] : m1_subset_1(k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f128,f70])).

fof(f4453,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f2703,f61])).

fof(f149,plain,
    ( ~ spl2_7
    | spl2_8 ),
    inference(avatar_split_clause,[],[f139,f146,f142])).

fof(f139,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f109,f67])).

fof(f109,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f108,f49])).

fof(f108,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f54,f50])).

fof(f84,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f51,f80,f76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:28:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (8846)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (8842)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (8841)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (8858)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (8840)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (8838)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (8857)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (8861)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (8850)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (8839)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (8843)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (8845)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (8851)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (8852)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (8854)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (8859)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (8848)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (8847)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (8844)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (8862)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (8860)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (8837)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (8856)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (8855)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (8849)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.48/0.55  % (8853)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.28/0.70  % (8846)Refutation not found, incomplete strategy% (8846)------------------------------
% 2.28/0.70  % (8846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.28/0.70  % (8846)Termination reason: Refutation not found, incomplete strategy
% 2.28/0.70  
% 2.28/0.70  % (8846)Memory used [KB]: 6268
% 2.28/0.70  % (8846)Time elapsed: 0.257 s
% 2.28/0.70  % (8846)------------------------------
% 2.28/0.70  % (8846)------------------------------
% 3.15/0.83  % (8847)Refutation found. Thanks to Tanya!
% 3.15/0.83  % SZS status Theorem for theBenchmark
% 3.15/0.83  % SZS output start Proof for theBenchmark
% 3.15/0.83  fof(f4664,plain,(
% 3.15/0.83    $false),
% 3.15/0.83    inference(avatar_sat_refutation,[],[f84,f149,f4466,f4498,f4592,f4656])).
% 3.15/0.83  fof(f4656,plain,(
% 3.15/0.83    ~spl2_2 | ~spl2_8),
% 3.15/0.83    inference(avatar_contradiction_clause,[],[f4655])).
% 3.15/0.83  fof(f4655,plain,(
% 3.15/0.83    $false | (~spl2_2 | ~spl2_8)),
% 3.15/0.83    inference(subsumption_resolution,[],[f4608,f4598])).
% 3.75/0.86  fof(f4598,plain,(
% 3.75/0.86    ~v3_pre_topc(sK1,sK0) | ~spl2_2),
% 3.75/0.86    inference(global_subsumption,[],[f52,f81])).
% 3.75/0.86  fof(f81,plain,(
% 3.75/0.86    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 3.75/0.86    inference(avatar_component_clause,[],[f80])).
% 3.75/0.86  fof(f80,plain,(
% 3.75/0.86    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.75/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.75/0.86  fof(f52,plain,(
% 3.75/0.86    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.75/0.86    inference(cnf_transformation,[],[f44])).
% 3.75/0.86  fof(f44,plain,(
% 3.75/0.86    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.75/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).
% 3.75/0.86  fof(f42,plain,(
% 3.75/0.86    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.75/0.86    introduced(choice_axiom,[])).
% 3.75/0.86  fof(f43,plain,(
% 3.75/0.86    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.75/0.86    introduced(choice_axiom,[])).
% 3.75/0.86  fof(f41,plain,(
% 3.75/0.86    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.75/0.86    inference(flattening,[],[f40])).
% 3.75/0.86  fof(f40,plain,(
% 3.75/0.86    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.75/0.86    inference(nnf_transformation,[],[f21])).
% 3.75/0.86  fof(f21,plain,(
% 3.75/0.86    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.75/0.86    inference(flattening,[],[f20])).
% 3.75/0.86  fof(f20,plain,(
% 3.75/0.86    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.75/0.86    inference(ennf_transformation,[],[f19])).
% 3.75/0.86  fof(f19,negated_conjecture,(
% 3.75/0.86    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.75/0.86    inference(negated_conjecture,[],[f18])).
% 3.75/0.86  fof(f18,conjecture,(
% 3.75/0.86    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 3.75/0.86  fof(f4608,plain,(
% 3.75/0.86    v3_pre_topc(sK1,sK0) | ~spl2_8),
% 3.75/0.86    inference(superposition,[],[f113,f148])).
% 3.75/0.86  fof(f148,plain,(
% 3.75/0.86    sK1 = k1_tops_1(sK0,sK1) | ~spl2_8),
% 3.75/0.86    inference(avatar_component_clause,[],[f146])).
% 3.75/0.86  fof(f146,plain,(
% 3.75/0.86    spl2_8 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.75/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 3.75/0.86  fof(f113,plain,(
% 3.75/0.86    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.75/0.86    inference(subsumption_resolution,[],[f112,f48])).
% 3.75/0.86  fof(f48,plain,(
% 3.75/0.86    v2_pre_topc(sK0)),
% 3.75/0.86    inference(cnf_transformation,[],[f44])).
% 3.75/0.86  fof(f112,plain,(
% 3.75/0.86    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0)),
% 3.75/0.86    inference(subsumption_resolution,[],[f111,f49])).
% 3.75/0.86  fof(f49,plain,(
% 3.75/0.86    l1_pre_topc(sK0)),
% 3.75/0.86    inference(cnf_transformation,[],[f44])).
% 3.75/0.86  fof(f111,plain,(
% 3.75/0.86    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 3.75/0.86    inference(resolution,[],[f63,f50])).
% 3.75/0.86  fof(f50,plain,(
% 3.75/0.86    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.75/0.86    inference(cnf_transformation,[],[f44])).
% 3.75/0.86  fof(f63,plain,(
% 3.75/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.75/0.86    inference(cnf_transformation,[],[f33])).
% 3.75/0.86  fof(f33,plain,(
% 3.75/0.86    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.75/0.86    inference(flattening,[],[f32])).
% 3.75/0.86  fof(f32,plain,(
% 3.75/0.86    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.75/0.86    inference(ennf_transformation,[],[f13])).
% 3.75/0.86  fof(f13,axiom,(
% 3.75/0.86    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.75/0.86  fof(f4592,plain,(
% 3.75/0.86    ~spl2_1 | spl2_2),
% 3.75/0.86    inference(avatar_contradiction_clause,[],[f4591])).
% 3.75/0.86  fof(f4591,plain,(
% 3.75/0.86    $false | (~spl2_1 | spl2_2)),
% 3.75/0.86    inference(subsumption_resolution,[],[f4566,f4508])).
% 3.75/0.86  fof(f4508,plain,(
% 3.75/0.86    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 3.75/0.86    inference(superposition,[],[f82,f162])).
% 3.75/0.86  fof(f162,plain,(
% 3.75/0.86    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2) = k4_xboole_0(k2_pre_topc(sK0,sK1),X2)) )),
% 3.75/0.86    inference(resolution,[],[f115,f71])).
% 3.75/0.86  fof(f71,plain,(
% 3.75/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 3.75/0.86    inference(cnf_transformation,[],[f37])).
% 3.75/0.86  fof(f37,plain,(
% 3.75/0.86    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.86    inference(ennf_transformation,[],[f8])).
% 3.75/0.86  fof(f8,axiom,(
% 3.75/0.86    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.75/0.86  fof(f115,plain,(
% 3.75/0.86    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.75/0.86    inference(subsumption_resolution,[],[f114,f49])).
% 3.75/0.86  fof(f114,plain,(
% 3.75/0.86    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 3.75/0.86    inference(resolution,[],[f64,f50])).
% 3.75/0.86  fof(f64,plain,(
% 3.75/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.75/0.86    inference(cnf_transformation,[],[f35])).
% 3.75/0.86  fof(f35,plain,(
% 3.75/0.86    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.75/0.86    inference(flattening,[],[f34])).
% 3.75/0.86  fof(f34,plain,(
% 3.75/0.86    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.75/0.86    inference(ennf_transformation,[],[f11])).
% 3.75/0.86  fof(f11,axiom,(
% 3.75/0.86    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 3.75/0.86  fof(f82,plain,(
% 3.75/0.86    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 3.75/0.86    inference(avatar_component_clause,[],[f80])).
% 3.75/0.86  fof(f4566,plain,(
% 3.75/0.86    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_1),
% 3.75/0.86    inference(superposition,[],[f820,f4507])).
% 3.75/0.86  fof(f4507,plain,(
% 3.75/0.86    sK1 = k1_tops_1(sK0,sK1) | ~spl2_1),
% 3.75/0.86    inference(subsumption_resolution,[],[f4145,f4500])).
% 3.75/0.86  fof(f4500,plain,(
% 3.75/0.86    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl2_1),
% 3.75/0.86    inference(subsumption_resolution,[],[f4499,f49])).
% 3.75/0.86  fof(f4499,plain,(
% 3.75/0.86    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_1),
% 3.75/0.86    inference(subsumption_resolution,[],[f315,f77])).
% 3.75/0.86  fof(f77,plain,(
% 3.75/0.86    v3_pre_topc(sK1,sK0) | ~spl2_1),
% 3.75/0.86    inference(avatar_component_clause,[],[f76])).
% 3.75/0.86  fof(f76,plain,(
% 3.75/0.86    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 3.75/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.75/0.86  fof(f315,plain,(
% 3.75/0.86    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 3.75/0.86    inference(resolution,[],[f125,f50])).
% 3.75/0.86  fof(f125,plain,(
% 3.75/0.86    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X0,X1) | r1_tarski(X0,k1_tops_1(X1,X0)) | ~l1_pre_topc(X1)) )),
% 3.75/0.86    inference(duplicate_literal_removal,[],[f122])).
% 3.75/0.86  fof(f122,plain,(
% 3.75/0.86    ( ! [X0,X1] : (r1_tarski(X0,k1_tops_1(X1,X0)) | ~v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 3.75/0.86    inference(resolution,[],[f57,f73])).
% 3.75/0.86  fof(f73,plain,(
% 3.75/0.86    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.75/0.86    inference(equality_resolution,[],[f66])).
% 3.75/0.86  fof(f66,plain,(
% 3.75/0.86    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.75/0.86    inference(cnf_transformation,[],[f46])).
% 3.75/0.86  fof(f46,plain,(
% 3.75/0.86    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.75/0.86    inference(flattening,[],[f45])).
% 3.75/0.86  fof(f45,plain,(
% 3.75/0.86    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.75/0.86    inference(nnf_transformation,[],[f1])).
% 3.75/0.86  fof(f1,axiom,(
% 3.75/0.86    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.75/0.86  fof(f57,plain,(
% 3.75/0.86    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.75/0.86    inference(cnf_transformation,[],[f27])).
% 3.75/0.86  fof(f27,plain,(
% 3.75/0.86    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.86    inference(flattening,[],[f26])).
% 3.75/0.86  fof(f26,plain,(
% 3.75/0.86    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.86    inference(ennf_transformation,[],[f16])).
% 3.75/0.86  fof(f16,axiom,(
% 3.75/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 3.75/0.86  fof(f4145,plain,(
% 3.75/0.86    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 3.75/0.86    inference(superposition,[],[f521,f3721])).
% 3.75/0.86  fof(f3721,plain,(
% 3.75/0.86    sK1 = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 3.75/0.86    inference(forward_demodulation,[],[f3699,f202])).
% 3.75/0.86  fof(f202,plain,(
% 3.75/0.86    sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 3.75/0.86    inference(forward_demodulation,[],[f201,f93])).
% 3.75/0.86  fof(f93,plain,(
% 3.75/0.86    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 3.75/0.86    inference(forward_demodulation,[],[f92,f91])).
% 3.75/0.86  fof(f91,plain,(
% 3.75/0.86    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 3.75/0.86    inference(resolution,[],[f60,f50])).
% 3.75/0.86  fof(f60,plain,(
% 3.75/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 3.75/0.86    inference(cnf_transformation,[],[f29])).
% 3.75/0.86  fof(f29,plain,(
% 3.75/0.86    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.86    inference(ennf_transformation,[],[f3])).
% 3.75/0.86  fof(f3,axiom,(
% 3.75/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.75/0.86  fof(f92,plain,(
% 3.75/0.86    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 3.75/0.86    inference(resolution,[],[f61,f50])).
% 3.75/0.86  fof(f61,plain,(
% 3.75/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 3.75/0.86    inference(cnf_transformation,[],[f30])).
% 3.75/0.86  fof(f30,plain,(
% 3.75/0.86    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.86    inference(ennf_transformation,[],[f7])).
% 3.75/0.86  fof(f7,axiom,(
% 3.75/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.75/0.86  fof(f201,plain,(
% 3.75/0.86    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 3.75/0.86    inference(forward_demodulation,[],[f179,f91])).
% 3.75/0.86  fof(f179,plain,(
% 3.75/0.86    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 3.75/0.86    inference(resolution,[],[f90,f60])).
% 3.75/0.86  fof(f90,plain,(
% 3.75/0.86    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.75/0.86    inference(resolution,[],[f59,f50])).
% 3.75/0.86  fof(f59,plain,(
% 3.75/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.75/0.86    inference(cnf_transformation,[],[f28])).
% 3.75/0.86  fof(f28,plain,(
% 3.75/0.86    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.86    inference(ennf_transformation,[],[f4])).
% 3.75/0.86  fof(f4,axiom,(
% 3.75/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.75/0.86  fof(f3699,plain,(
% 3.75/0.86    k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 3.75/0.86    inference(superposition,[],[f1281,f1358])).
% 3.75/0.86  fof(f1358,plain,(
% 3.75/0.86    k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 3.75/0.86    inference(forward_demodulation,[],[f1357,f270])).
% 3.75/0.86  fof(f270,plain,(
% 3.75/0.86    k4_xboole_0(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 3.75/0.86    inference(forward_demodulation,[],[f265,f91])).
% 3.75/0.86  fof(f265,plain,(
% 3.75/0.86    k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 3.75/0.86    inference(resolution,[],[f116,f90])).
% 3.75/0.86  fof(f116,plain,(
% 3.75/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,X0) = X0) )),
% 3.75/0.86    inference(resolution,[],[f72,f50])).
% 3.75/0.86  fof(f72,plain,(
% 3.75/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.75/0.86    inference(cnf_transformation,[],[f39])).
% 3.75/0.86  fof(f39,plain,(
% 3.75/0.86    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.86    inference(flattening,[],[f38])).
% 3.75/0.86  fof(f38,plain,(
% 3.75/0.86    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X1) = X1 | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.75/0.86    inference(ennf_transformation,[],[f6])).
% 3.75/0.86  fof(f6,axiom,(
% 3.75/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X1) = X1)),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k4_subset_1)).
% 3.75/0.86  fof(f1357,plain,(
% 3.75/0.86    k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 3.75/0.86    inference(forward_demodulation,[],[f1356,f238])).
% 3.75/0.86  fof(f238,plain,(
% 3.75/0.86    ( ! [X7] : (k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,X7)) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X7))) )),
% 3.75/0.86    inference(forward_demodulation,[],[f217,f110])).
% 3.75/0.86  fof(f110,plain,(
% 3.75/0.86    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 3.75/0.86    inference(resolution,[],[f71,f50])).
% 3.75/0.86  fof(f217,plain,(
% 3.75/0.86    ( ! [X7] : (k4_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X7)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X7))) )),
% 3.75/0.86    inference(resolution,[],[f105,f60])).
% 3.75/0.86  fof(f105,plain,(
% 3.75/0.86    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.75/0.86    inference(resolution,[],[f70,f50])).
% 3.75/0.86  fof(f70,plain,(
% 3.75/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 3.75/0.86    inference(cnf_transformation,[],[f36])).
% 3.75/0.86  fof(f36,plain,(
% 3.75/0.86    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.86    inference(ennf_transformation,[],[f5])).
% 3.75/0.86  fof(f5,axiom,(
% 3.75/0.86    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 3.75/0.86  fof(f1356,plain,(
% 3.75/0.86    k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 3.75/0.86    inference(forward_demodulation,[],[f1355,f110])).
% 3.75/0.86  fof(f1355,plain,(
% 3.75/0.86    k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 3.75/0.86    inference(forward_demodulation,[],[f1310,f91])).
% 3.75/0.86  fof(f1310,plain,(
% 3.75/0.86    k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 3.75/0.86    inference(resolution,[],[f205,f50])).
% 3.75/0.86  fof(f205,plain,(
% 3.75/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(u1_struct_0(sK0),sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k4_xboole_0(u1_struct_0(sK0),sK1))) )),
% 3.75/0.86    inference(forward_demodulation,[],[f181,f91])).
% 3.75/0.86  fof(f181,plain,(
% 3.75/0.86    ( ! [X0] : (k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X0,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.75/0.86    inference(resolution,[],[f90,f62])).
% 3.75/0.86  fof(f62,plain,(
% 3.75/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.75/0.86    inference(cnf_transformation,[],[f31])).
% 3.75/0.86  fof(f31,plain,(
% 3.75/0.86    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.86    inference(ennf_transformation,[],[f9])).
% 3.75/0.86  fof(f9,axiom,(
% 3.75/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).
% 3.75/0.86  fof(f1281,plain,(
% 3.75/0.86    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,X0)))) )),
% 3.75/0.86    inference(superposition,[],[f273,f240])).
% 3.75/0.86  fof(f240,plain,(
% 3.75/0.86    ( ! [X8] : (k4_xboole_0(sK1,X8) = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,X8)))) )),
% 3.75/0.86    inference(forward_demodulation,[],[f239,f238])).
% 3.75/0.86  fof(f239,plain,(
% 3.75/0.86    ( ! [X8] : (k4_xboole_0(sK1,X8) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X8)))) )),
% 3.75/0.86    inference(forward_demodulation,[],[f218,f110])).
% 3.75/0.86  fof(f218,plain,(
% 3.75/0.86    ( ! [X8] : (k7_subset_1(u1_struct_0(sK0),sK1,X8) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X8)))) )),
% 3.75/0.86    inference(resolution,[],[f105,f61])).
% 3.75/0.86  fof(f273,plain,(
% 3.75/0.86    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,X3)) = k3_subset_1(X2,k4_xboole_0(X2,X3))) )),
% 3.75/0.86    inference(resolution,[],[f87,f60])).
% 3.75/0.86  fof(f87,plain,(
% 3.75/0.86    ( ! [X2,X1] : (m1_subset_1(k4_xboole_0(X1,X2),k1_zfmisc_1(X1))) )),
% 3.75/0.86    inference(resolution,[],[f69,f58])).
% 3.75/0.86  fof(f58,plain,(
% 3.75/0.86    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.75/0.86    inference(cnf_transformation,[],[f2])).
% 3.75/0.86  fof(f2,axiom,(
% 3.75/0.86    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.75/0.86  fof(f69,plain,(
% 3.75/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.75/0.86    inference(cnf_transformation,[],[f47])).
% 3.75/0.86  fof(f47,plain,(
% 3.75/0.86    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.75/0.86    inference(nnf_transformation,[],[f10])).
% 3.75/0.86  fof(f10,axiom,(
% 3.75/0.86    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.75/0.86  fof(f521,plain,(
% 3.75/0.86    ( ! [X2] : (~r1_tarski(k4_xboole_0(sK1,X2),k1_tops_1(sK0,k4_xboole_0(sK1,X2))) | k4_xboole_0(sK1,X2) = k1_tops_1(sK0,k4_xboole_0(sK1,X2))) )),
% 3.75/0.86    inference(resolution,[],[f234,f67])).
% 3.75/0.86  fof(f67,plain,(
% 3.75/0.86    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.75/0.86    inference(cnf_transformation,[],[f46])).
% 3.75/0.86  fof(f234,plain,(
% 3.75/0.86    ( ! [X4] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X4)),k4_xboole_0(sK1,X4))) )),
% 3.75/0.86    inference(forward_demodulation,[],[f233,f110])).
% 3.75/0.86  fof(f233,plain,(
% 3.75/0.86    ( ! [X4] : (r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X4)),k7_subset_1(u1_struct_0(sK0),sK1,X4))) )),
% 3.75/0.86    inference(subsumption_resolution,[],[f214,f49])).
% 3.75/0.86  fof(f214,plain,(
% 3.75/0.86    ( ! [X4] : (r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X4)),k7_subset_1(u1_struct_0(sK0),sK1,X4)) | ~l1_pre_topc(sK0)) )),
% 3.75/0.86    inference(resolution,[],[f105,f54])).
% 3.75/0.86  fof(f54,plain,(
% 3.75/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 3.75/0.86    inference(cnf_transformation,[],[f23])).
% 3.75/0.86  fof(f23,plain,(
% 3.75/0.86    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.86    inference(ennf_transformation,[],[f15])).
% 3.75/0.86  fof(f15,axiom,(
% 3.75/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 3.75/0.86  fof(f820,plain,(
% 3.75/0.86    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.75/0.86    inference(superposition,[],[f162,f120])).
% 3.75/0.86  fof(f120,plain,(
% 3.75/0.86    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.75/0.86    inference(subsumption_resolution,[],[f119,f49])).
% 3.75/0.86  fof(f119,plain,(
% 3.75/0.86    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 3.75/0.86    inference(resolution,[],[f56,f50])).
% 3.75/0.86  fof(f56,plain,(
% 3.75/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 3.75/0.86    inference(cnf_transformation,[],[f25])).
% 3.75/0.86  fof(f25,plain,(
% 3.75/0.86    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.86    inference(ennf_transformation,[],[f14])).
% 3.75/0.86  fof(f14,axiom,(
% 3.75/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.75/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.75/0.86  fof(f4498,plain,(
% 3.75/0.86    spl2_2 | spl2_7),
% 3.75/0.86    inference(avatar_contradiction_clause,[],[f4497])).
% 3.75/0.87  fof(f4497,plain,(
% 3.75/0.87    $false | (spl2_2 | spl2_7)),
% 3.75/0.87    inference(global_subsumption,[],[f51,f4473,f82])).
% 3.75/0.87  fof(f4473,plain,(
% 3.75/0.87    ~v3_pre_topc(sK1,sK0) | spl2_7),
% 3.75/0.87    inference(subsumption_resolution,[],[f4133,f144])).
% 3.75/0.87  fof(f144,plain,(
% 3.75/0.87    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl2_7),
% 3.75/0.87    inference(avatar_component_clause,[],[f142])).
% 3.75/0.87  fof(f142,plain,(
% 3.75/0.87    spl2_7 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.75/0.87    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 3.75/0.87  fof(f4133,plain,(
% 3.75/0.87    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.75/0.87    inference(superposition,[],[f397,f3721])).
% 3.75/0.87  fof(f397,plain,(
% 3.75/0.87    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(sK1,X0),sK0) | r1_tarski(k4_xboole_0(sK1,X0),k1_tops_1(sK0,sK1))) )),
% 3.75/0.87    inference(subsumption_resolution,[],[f396,f49])).
% 3.75/0.87  fof(f396,plain,(
% 3.75/0.87    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(sK1,X0),sK0) | r1_tarski(k4_xboole_0(sK1,X0),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)) )),
% 3.75/0.87    inference(subsumption_resolution,[],[f378,f50])).
% 3.75/0.87  fof(f378,plain,(
% 3.75/0.87    ( ! [X0] : (~v3_pre_topc(k4_xboole_0(sK1,X0),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k4_xboole_0(sK1,X0),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)) )),
% 3.75/0.87    inference(resolution,[],[f245,f123])).
% 3.75/0.87  fof(f123,plain,(
% 3.75/0.87    ( ! [X4,X2,X3] : (~m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(u1_struct_0(X4))) | ~v3_pre_topc(k4_xboole_0(X2,X3),X4) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4))) | r1_tarski(k4_xboole_0(X2,X3),k1_tops_1(X4,X2)) | ~l1_pre_topc(X4)) )),
% 3.75/0.87    inference(resolution,[],[f57,f58])).
% 3.75/0.87  fof(f245,plain,(
% 3.75/0.87    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.75/0.87    inference(superposition,[],[f105,f110])).
% 3.75/0.87  fof(f51,plain,(
% 3.75/0.87    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.75/0.87    inference(cnf_transformation,[],[f44])).
% 3.75/0.87  fof(f4466,plain,(
% 3.75/0.87    ~spl2_2 | spl2_8),
% 3.75/0.87    inference(avatar_contradiction_clause,[],[f4465])).
% 3.75/0.87  fof(f4465,plain,(
% 3.75/0.87    $false | (~spl2_2 | spl2_8)),
% 3.75/0.87    inference(subsumption_resolution,[],[f4464,f147])).
% 3.75/0.87  fof(f147,plain,(
% 3.75/0.87    sK1 != k1_tops_1(sK0,sK1) | spl2_8),
% 3.75/0.87    inference(avatar_component_clause,[],[f146])).
% 3.75/0.87  fof(f4464,plain,(
% 3.75/0.87    sK1 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 3.75/0.87    inference(forward_demodulation,[],[f4463,f2304])).
% 3.75/0.87  fof(f2304,plain,(
% 3.75/0.87    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_2),
% 3.75/0.87    inference(superposition,[],[f353,f819])).
% 3.75/0.87  fof(f819,plain,(
% 3.75/0.87    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 3.75/0.87    inference(superposition,[],[f162,f81])).
% 3.75/0.87  fof(f353,plain,(
% 3.75/0.87    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))),
% 3.75/0.87    inference(forward_demodulation,[],[f347,f346])).
% 3.75/0.87  fof(f346,plain,(
% 3.75/0.87    k3_subset_1(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.75/0.87    inference(resolution,[],[f128,f60])).
% 3.75/0.87  fof(f128,plain,(
% 3.75/0.87    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.75/0.87    inference(resolution,[],[f107,f69])).
% 3.75/0.87  fof(f107,plain,(
% 3.75/0.87    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 3.75/0.87    inference(subsumption_resolution,[],[f106,f49])).
% 3.75/0.87  fof(f106,plain,(
% 3.75/0.87    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 3.75/0.87    inference(resolution,[],[f53,f50])).
% 3.75/0.87  fof(f53,plain,(
% 3.75/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 3.75/0.87    inference(cnf_transformation,[],[f22])).
% 3.75/0.87  fof(f22,plain,(
% 3.75/0.87    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.87    inference(ennf_transformation,[],[f12])).
% 3.75/0.87  fof(f12,axiom,(
% 3.75/0.87    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 3.75/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 3.75/0.87  fof(f347,plain,(
% 3.75/0.87    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))),
% 3.75/0.87    inference(resolution,[],[f128,f61])).
% 3.75/0.87  fof(f4463,plain,(
% 3.75/0.87    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 3.75/0.87    inference(forward_demodulation,[],[f4453,f4462])).
% 3.75/0.87  fof(f4462,plain,(
% 3.75/0.87    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.75/0.87    inference(forward_demodulation,[],[f4452,f820])).
% 3.75/0.87  fof(f4452,plain,(
% 3.75/0.87    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.75/0.87    inference(resolution,[],[f2703,f60])).
% 3.75/0.87  fof(f2703,plain,(
% 3.75/0.87    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.75/0.87    inference(resolution,[],[f2553,f69])).
% 3.75/0.87  fof(f2553,plain,(
% 3.75/0.87    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 3.75/0.87    inference(superposition,[],[f2294,f262])).
% 3.75/0.87  fof(f262,plain,(
% 3.75/0.87    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.75/0.87    inference(superposition,[],[f118,f110])).
% 3.75/0.87  fof(f118,plain,(
% 3.75/0.87    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.75/0.87    inference(subsumption_resolution,[],[f117,f49])).
% 3.75/0.87  fof(f117,plain,(
% 3.75/0.87    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 3.75/0.87    inference(resolution,[],[f55,f50])).
% 3.75/0.87  fof(f55,plain,(
% 3.75/0.87    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 3.75/0.87    inference(cnf_transformation,[],[f24])).
% 3.75/0.87  fof(f24,plain,(
% 3.75/0.87    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.87    inference(ennf_transformation,[],[f17])).
% 3.75/0.87  fof(f17,axiom,(
% 3.75/0.87    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.75/0.87    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.75/0.87  fof(f2294,plain,(
% 3.75/0.87    ( ! [X5] : (r1_tarski(k4_xboole_0(sK1,X5),k2_pre_topc(sK0,sK1))) )),
% 3.75/0.87    inference(forward_demodulation,[],[f2281,f351])).
% 3.75/0.87  fof(f351,plain,(
% 3.75/0.87    ( ! [X2] : (k4_xboole_0(sK1,X2) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X2)) )),
% 3.75/0.87    inference(resolution,[],[f128,f71])).
% 3.75/0.87  fof(f2281,plain,(
% 3.75/0.87    ( ! [X5] : (r1_tarski(k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X5),k2_pre_topc(sK0,sK1))) )),
% 3.75/0.87    inference(resolution,[],[f350,f68])).
% 3.75/0.87  fof(f68,plain,(
% 3.75/0.87    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.75/0.87    inference(cnf_transformation,[],[f47])).
% 3.75/0.87  fof(f350,plain,(
% 3.75/0.87    ( ! [X1] : (m1_subset_1(k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) )),
% 3.75/0.87    inference(resolution,[],[f128,f70])).
% 3.75/0.87  fof(f4453,plain,(
% 3.75/0.87    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))),
% 3.75/0.87    inference(resolution,[],[f2703,f61])).
% 3.75/0.87  fof(f149,plain,(
% 3.75/0.87    ~spl2_7 | spl2_8),
% 3.75/0.87    inference(avatar_split_clause,[],[f139,f146,f142])).
% 3.75/0.87  fof(f139,plain,(
% 3.75/0.87    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.75/0.87    inference(resolution,[],[f109,f67])).
% 3.75/0.87  fof(f109,plain,(
% 3.75/0.87    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.75/0.87    inference(subsumption_resolution,[],[f108,f49])).
% 3.75/0.87  fof(f108,plain,(
% 3.75/0.87    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 3.75/0.87    inference(resolution,[],[f54,f50])).
% 3.75/0.87  fof(f84,plain,(
% 3.75/0.87    spl2_1 | spl2_2),
% 3.75/0.87    inference(avatar_split_clause,[],[f51,f80,f76])).
% 3.75/0.87  % SZS output end Proof for theBenchmark
% 3.75/0.87  % (8847)------------------------------
% 3.75/0.87  % (8847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.87  % (8847)Termination reason: Refutation
% 3.75/0.87  
% 3.75/0.87  % (8847)Memory used [KB]: 14456
% 3.75/0.87  % (8847)Time elapsed: 0.436 s
% 3.75/0.87  % (8847)------------------------------
% 3.75/0.87  % (8847)------------------------------
% 3.75/0.87  % (8836)Success in time 0.503 s
%------------------------------------------------------------------------------
