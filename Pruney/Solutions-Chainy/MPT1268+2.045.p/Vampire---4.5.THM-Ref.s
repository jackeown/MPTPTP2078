%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 485 expanded)
%              Number of leaves         :   23 ( 150 expanded)
%              Depth                    :   22
%              Number of atoms          :  526 (4192 expanded)
%              Number of equality atoms :   78 ( 655 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32083)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f338,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f100,f176,f337])).

fof(f337,plain,
    ( ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f335,f80])).

fof(f80,plain,
    ( k1_xboole_0 != sK2
    | spl7_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f335,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(backward_demodulation,[],[f205,f334])).

fof(f334,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f307,f256])).

fof(f256,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl7_1 ),
    inference(trivial_inequality_removal,[],[f255])).

fof(f255,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl7_1 ),
    inference(superposition,[],[f63,f196])).

fof(f196,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f150,f193])).

fof(f193,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f192,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

% (32074)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f33,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_tops_1(X1,sK0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK0)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK0)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_tops_1(sK1,sK0) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK0)
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

% (32071)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f34,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK2
      & v3_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

% (32073)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(f192,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f102,f75])).

fof(f75,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f102,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f150,plain,(
    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f111,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f111,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f101,f40])).

fof(f101,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f53])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f307,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,X0)) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f298,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f298,plain,
    ( ! [X1] :
        ( r1_xboole_0(sK2,X1)
        | ~ r1_xboole_0(k1_xboole_0,X1) )
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f280,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f280,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f270,f90])).

fof(f90,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl7_4
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f270,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(sK2,sK1)
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(superposition,[],[f195,f234])).

fof(f234,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f233,f142])).

fof(f142,plain,(
    sP6 ),
    inference(subsumption_resolution,[],[f141,f40])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK0)
    | sP6 ),
    inference(subsumption_resolution,[],[f140,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f140,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | sP6 ),
    inference(resolution,[],[f108,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ sP5(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | sP6 ) ),
    inference(cnf_transformation,[],[f71_D])).

fof(f71_D,plain,
    ( ! [X0] :
        ( ~ sP5(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
  <=> ~ sP6 ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f108,plain,(
    sP5(sK0) ),
    inference(resolution,[],[f41,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP5(X0) ) ),
    inference(cnf_transformation,[],[f69_D])).

fof(f69_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    <=> ~ sP5(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f233,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ sP6
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f232,f40])).

fof(f232,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ sP6
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f214,f85])).

fof(f85,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl7_3
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f214,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | sK2 = k1_tops_1(sK0,sK2)
    | ~ l1_pre_topc(sK0)
    | ~ sP6
    | ~ spl7_5 ),
    inference(resolution,[],[f95,f72])).

fof(f72,plain,(
    ! [X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3
      | ~ l1_pre_topc(X1)
      | ~ sP6 ) ),
    inference(general_splitting,[],[f70,f71_D])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ sP5(X0) ) ),
    inference(general_splitting,[],[f51,f69_D])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f95,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f195,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f171,f193])).

fof(f171,plain,(
    ! [X0] :
      ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f169,f145])).

fof(f145,plain,(
    ! [X0] :
      ( r1_tarski(X0,u1_struct_0(sK0))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f110,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f110,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f169,plain,(
    ! [X0] :
      ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f114,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f104,f40])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f205,plain,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,sK1))
    | ~ spl7_4 ),
    inference(resolution,[],[f90,f62])).

fof(f176,plain,
    ( spl7_1
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl7_1
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f174,f113])).

fof(f113,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f112,f40])).

fof(f112,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f103,f76])).

fof(f76,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f103,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f174,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f173,f111])).

fof(f173,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl7_6 ),
    inference(resolution,[],[f157,f116])).

fof(f116,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f115,f39])).

fof(f115,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f105,f40])).

fof(f105,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f41,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f157,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0 )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,sK1) )
    | ~ spl7_6 ),
    inference(resolution,[],[f138,f145])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl7_6 ),
    inference(resolution,[],[f99,f59])).

fof(f99,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_6
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f100,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f42,f98,f74])).

fof(f42,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f43,f93,f74])).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f44,f88,f74])).

fof(f44,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f45,f83,f74])).

fof(f45,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f46,f78,f74])).

fof(f46,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (32069)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (32077)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (32077)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  % (32083)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  fof(f338,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f100,f176,f337])).
% 0.20/0.53  fof(f337,plain,(
% 0.20/0.53    ~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f336])).
% 0.20/0.53  fof(f336,plain,(
% 0.20/0.53    $false | (~spl7_1 | spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f335,f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    k1_xboole_0 != sK2 | spl7_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    spl7_2 <=> k1_xboole_0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.53  fof(f335,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.53    inference(backward_demodulation,[],[f205,f334])).
% 0.20/0.53  fof(f334,plain,(
% 0.20/0.53    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK1)) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.53    inference(resolution,[],[f307,f256])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    r1_xboole_0(k1_xboole_0,sK1) | ~spl7_1),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f255])).
% 0.20/0.53  fof(f255,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,sK1) | ~spl7_1),
% 0.20/0.53    inference(superposition,[],[f63,f196])).
% 0.20/0.53  fof(f196,plain,(
% 0.20/0.53    k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,sK1)) | ~spl7_1),
% 0.20/0.53    inference(forward_demodulation,[],[f150,f193])).
% 0.20/0.53  fof(f193,plain,(
% 0.20/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl7_1),
% 0.20/0.53    inference(subsumption_resolution,[],[f192,f40])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  % (32074)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  % (32071)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.53    inference(rectify,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f29])).
% 0.20/0.53  % (32073)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.53    inference(negated_conjecture,[],[f12])).
% 0.20/0.53  fof(f12,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.20/0.53  fof(f192,plain,(
% 0.20/0.53    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~spl7_1),
% 0.20/0.53    inference(subsumption_resolution,[],[f102,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    v2_tops_1(sK1,sK0) | ~spl7_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    spl7_1 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.53    inference(resolution,[],[f41,f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1))),
% 0.20/0.53    inference(resolution,[],[f111,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f54,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.53    inference(subsumption_resolution,[],[f101,f40])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.20/0.53    inference(resolution,[],[f41,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f57,f53])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.53  fof(f307,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,X0))) ) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.53    inference(resolution,[],[f298,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f56,f53])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f37])).
% 0.20/0.53  fof(f298,plain,(
% 0.20/0.53    ( ! [X1] : (r1_xboole_0(sK2,X1) | ~r1_xboole_0(k1_xboole_0,X1)) ) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.53    inference(resolution,[],[f280,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.53  fof(f280,plain,(
% 0.20/0.53    r1_tarski(sK2,k1_xboole_0) | (~spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f270,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    r1_tarski(sK2,sK1) | ~spl7_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    spl7_4 <=> r1_tarski(sK2,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    r1_tarski(sK2,k1_xboole_0) | ~r1_tarski(sK2,sK1) | (~spl7_1 | ~spl7_3 | ~spl7_5)),
% 0.20/0.53    inference(superposition,[],[f195,f234])).
% 0.20/0.53  fof(f234,plain,(
% 0.20/0.53    sK2 = k1_tops_1(sK0,sK2) | (~spl7_3 | ~spl7_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f233,f142])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    sP6),
% 0.20/0.53    inference(subsumption_resolution,[],[f141,f40])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | sP6),
% 0.20/0.53    inference(subsumption_resolution,[],[f140,f39])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f35])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | sP6),
% 0.20/0.53    inference(resolution,[],[f108,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    ( ! [X0] : (~sP5(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | sP6) )),
% 0.20/0.53    inference(cnf_transformation,[],[f71_D])).
% 0.20/0.53  fof(f71_D,plain,(
% 0.20/0.53    ( ! [X0] : (~sP5(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) <=> ~sP6),
% 0.20/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    sP5(sK0)),
% 0.20/0.53    inference(resolution,[],[f41,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP5(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f69_D])).
% 0.20/0.53  fof(f69_D,plain,(
% 0.20/0.53    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) <=> ~sP5(X0)) )),
% 0.20/0.53    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.53  fof(f233,plain,(
% 0.20/0.53    sK2 = k1_tops_1(sK0,sK2) | ~sP6 | (~spl7_3 | ~spl7_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f232,f40])).
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    sK2 = k1_tops_1(sK0,sK2) | ~l1_pre_topc(sK0) | ~sP6 | (~spl7_3 | ~spl7_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f214,f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    v3_pre_topc(sK2,sK0) | ~spl7_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f83])).
% 0.20/0.53  fof(f83,plain,(
% 0.20/0.53    spl7_3 <=> v3_pre_topc(sK2,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    ~v3_pre_topc(sK2,sK0) | sK2 = k1_tops_1(sK0,sK2) | ~l1_pre_topc(sK0) | ~sP6 | ~spl7_5),
% 0.20/0.53    inference(resolution,[],[f95,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~sP6) )),
% 0.20/0.53    inference(general_splitting,[],[f70,f71_D])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~sP5(X0)) )),
% 0.20/0.53    inference(general_splitting,[],[f51,f69_D])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    spl7_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.53  fof(f195,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,X0),k1_xboole_0) | ~r1_tarski(X0,sK1)) ) | ~spl7_1),
% 0.20/0.53    inference(forward_demodulation,[],[f171,f193])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f169,f145])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1)) )),
% 0.20/0.53    inference(resolution,[],[f110,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.53  fof(f110,plain,(
% 0.20/0.53    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.53    inference(resolution,[],[f41,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.20/0.53    inference(resolution,[],[f114,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f104,f40])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f41,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    sK2 = k1_setfam_1(k2_tarski(sK2,sK1)) | ~spl7_4),
% 0.20/0.53    inference(resolution,[],[f90,f62])).
% 0.20/0.54  fof(f176,plain,(
% 0.20/0.54    spl7_1 | ~spl7_6),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f175])).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    $false | (spl7_1 | ~spl7_6)),
% 0.20/0.54    inference(subsumption_resolution,[],[f174,f113])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl7_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f112,f40])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | spl7_1),
% 0.20/0.54    inference(subsumption_resolution,[],[f103,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    ~v2_tops_1(sK1,sK0) | spl7_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f74])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.54    inference(resolution,[],[f41,f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f36])).
% 0.20/0.54  fof(f174,plain,(
% 0.20/0.54    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl7_6),
% 0.20/0.54    inference(subsumption_resolution,[],[f173,f111])).
% 0.20/0.54  fof(f173,plain,(
% 0.20/0.54    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl7_6),
% 0.20/0.54    inference(resolution,[],[f157,f116])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f115,f39])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f105,f40])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.20/0.54    inference(resolution,[],[f41,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1) | k1_xboole_0 = X0) ) | ~spl7_6),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f156])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK1)) ) | ~spl7_6),
% 0.20/0.54    inference(resolution,[],[f138,f145])).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | k1_xboole_0 = X0) ) | ~spl7_6),
% 0.20/0.54    inference(resolution,[],[f99,f59])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0)) ) | ~spl7_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f98])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    spl7_6 <=> ! [X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(X3,sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    spl7_1 | spl7_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f42,f98,f74])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ~spl7_1 | spl7_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f43,f93,f74])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ~spl7_1 | spl7_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f44,f88,f74])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ~spl7_1 | spl7_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f45,f83,f74])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ~spl7_1 | ~spl7_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f46,f78,f74])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (32077)------------------------------
% 0.20/0.54  % (32077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32077)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (32077)Memory used [KB]: 10874
% 0.20/0.54  % (32077)Time elapsed: 0.109 s
% 0.20/0.54  % (32077)------------------------------
% 0.20/0.54  % (32077)------------------------------
% 0.20/0.54  % (32092)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (32095)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (32068)Success in time 0.18 s
%------------------------------------------------------------------------------
