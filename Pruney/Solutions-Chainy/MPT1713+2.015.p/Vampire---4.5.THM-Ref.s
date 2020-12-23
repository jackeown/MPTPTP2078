%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:52 EST 2020

% Result     : Theorem 0.98s
% Output     : Refutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 234 expanded)
%              Number of leaves         :   18 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  259 (1666 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f141,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f100,f140])).

fof(f140,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f83,f138])).

fof(f138,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK1))
    | ~ spl5_1 ),
    inference(backward_demodulation,[],[f112,f134])).

fof(f134,plain,(
    u1_struct_0(sK1) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f132,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f132,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f105,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f105,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unit_resulting_resolution,[],[f72,f45,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f45,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

% (14043)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f29,plain,
    ( ( r1_tsep_1(sK2,sK1)
      | r1_tsep_1(sK1,sK2) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( r1_tsep_1(X2,X1)
              | r1_tsep_1(X1,X2) )
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( r1_tsep_1(X2,sK1)
            | r1_tsep_1(sK1,X2) )
          & m1_pre_topc(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ( r1_tsep_1(X2,sK1)
          | r1_tsep_1(sK1,X2) )
        & m1_pre_topc(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( r1_tsep_1(sK2,sK1)
        | r1_tsep_1(sK1,sK2) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f72,plain,(
    l1_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f44,f40,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f112,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f108,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f108,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f74,f77,f64,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f64,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_1
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f77,plain,(
    l1_struct_0(sK2) ),
    inference(unit_resulting_resolution,[],[f72,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f74,plain,(
    l1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f71,f49])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(unit_resulting_resolution,[],[f42,f40,f50])).

fof(f42,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f80,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f80,plain,(
    ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f74,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f100,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f77,f74,f63,f68,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f68,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_2
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f63,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f69,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f46,f66,f62])).

fof(f46,plain,
    ( r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:29:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (794198016)
% 0.21/0.37  ipcrm: permission denied for id (794230786)
% 0.21/0.41  ipcrm: permission denied for id (794394654)
% 0.21/0.41  ipcrm: permission denied for id (794427425)
% 0.21/0.43  ipcrm: permission denied for id (794492977)
% 0.21/0.43  ipcrm: permission denied for id (794525746)
% 0.22/0.46  ipcrm: permission denied for id (794591304)
% 0.22/0.46  ipcrm: permission denied for id (794656842)
% 0.22/0.47  ipcrm: permission denied for id (794755159)
% 0.22/0.48  ipcrm: permission denied for id (794820702)
% 0.22/0.49  ipcrm: permission denied for id (794853477)
% 0.22/0.49  ipcrm: permission denied for id (794886246)
% 0.22/0.50  ipcrm: permission denied for id (794951785)
% 0.22/0.50  ipcrm: permission denied for id (794984557)
% 0.22/0.51  ipcrm: permission denied for id (795050101)
% 0.22/0.53  ipcrm: permission denied for id (795082879)
% 0.75/0.63  % (14054)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.98/0.65  % (14054)Refutation found. Thanks to Tanya!
% 0.98/0.65  % SZS status Theorem for theBenchmark
% 0.98/0.65  % SZS output start Proof for theBenchmark
% 0.98/0.65  fof(f141,plain,(
% 0.98/0.65    $false),
% 0.98/0.65    inference(avatar_sat_refutation,[],[f69,f100,f140])).
% 0.98/0.65  fof(f140,plain,(
% 0.98/0.65    ~spl5_1),
% 0.98/0.65    inference(avatar_contradiction_clause,[],[f139])).
% 0.98/0.65  fof(f139,plain,(
% 0.98/0.65    $false | ~spl5_1),
% 0.98/0.65    inference(subsumption_resolution,[],[f83,f138])).
% 0.98/0.65  fof(f138,plain,(
% 0.98/0.65    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK1))) ) | ~spl5_1),
% 0.98/0.65    inference(backward_demodulation,[],[f112,f134])).
% 0.98/0.65  fof(f134,plain,(
% 0.98/0.65    u1_struct_0(sK1) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f132,f57])).
% 0.98/0.65  fof(f57,plain,(
% 0.98/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.98/0.65    inference(cnf_transformation,[],[f23])).
% 0.98/0.65  fof(f23,plain,(
% 0.98/0.65    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.98/0.65    inference(ennf_transformation,[],[f3])).
% 0.98/0.65  fof(f3,axiom,(
% 0.98/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.98/0.65  fof(f132,plain,(
% 0.98/0.65    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f105,f59])).
% 0.98/0.65  fof(f59,plain,(
% 0.98/0.65    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.98/0.65    inference(cnf_transformation,[],[f37])).
% 0.98/0.65  fof(f37,plain,(
% 0.98/0.65    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.98/0.65    inference(nnf_transformation,[],[f4])).
% 0.98/0.65  fof(f4,axiom,(
% 0.98/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.98/0.65  fof(f105,plain,(
% 0.98/0.65    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f72,f45,f51])).
% 0.98/0.65  fof(f51,plain,(
% 0.98/0.65    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.98/0.65    inference(cnf_transformation,[],[f19])).
% 0.98/0.65  fof(f19,plain,(
% 0.98/0.65    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.98/0.65    inference(ennf_transformation,[],[f10])).
% 0.98/0.65  fof(f10,axiom,(
% 0.98/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.98/0.65  fof(f45,plain,(
% 0.98/0.65    m1_pre_topc(sK1,sK2)),
% 0.98/0.65    inference(cnf_transformation,[],[f29])).
% 0.98/0.65  % (14043)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.98/0.65  fof(f29,plain,(
% 0.98/0.65    (((r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.98/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f28,f27,f26])).
% 0.98/0.65  fof(f26,plain,(
% 0.98/0.65    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.98/0.65    introduced(choice_axiom,[])).
% 0.98/0.65  fof(f27,plain,(
% 0.98/0.65    ? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : ((r1_tsep_1(X2,sK1) | r1_tsep_1(sK1,X2)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.98/0.65    introduced(choice_axiom,[])).
% 0.98/0.65  fof(f28,plain,(
% 0.98/0.65    ? [X2] : ((r1_tsep_1(X2,sK1) | r1_tsep_1(sK1,X2)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => ((r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.98/0.65    introduced(choice_axiom,[])).
% 0.98/0.65  fof(f15,plain,(
% 0.98/0.65    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.98/0.65    inference(flattening,[],[f14])).
% 0.98/0.65  fof(f14,plain,(
% 0.98/0.65    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.98/0.65    inference(ennf_transformation,[],[f12])).
% 0.98/0.65  fof(f12,negated_conjecture,(
% 0.98/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.98/0.65    inference(negated_conjecture,[],[f11])).
% 0.98/0.65  fof(f11,conjecture,(
% 0.98/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.98/0.65  fof(f72,plain,(
% 0.98/0.65    l1_pre_topc(sK2)),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f44,f40,f50])).
% 0.98/0.65  fof(f50,plain,(
% 0.98/0.65    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.98/0.65    inference(cnf_transformation,[],[f18])).
% 0.98/0.65  fof(f18,plain,(
% 0.98/0.65    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.98/0.65    inference(ennf_transformation,[],[f6])).
% 0.98/0.65  fof(f6,axiom,(
% 0.98/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.98/0.65  fof(f40,plain,(
% 0.98/0.65    l1_pre_topc(sK0)),
% 0.98/0.65    inference(cnf_transformation,[],[f29])).
% 0.98/0.65  fof(f44,plain,(
% 0.98/0.65    m1_pre_topc(sK2,sK0)),
% 0.98/0.65    inference(cnf_transformation,[],[f29])).
% 0.98/0.65  fof(f112,plain,(
% 0.98/0.65    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))) ) | ~spl5_1),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f108,f56])).
% 0.98/0.65  fof(f56,plain,(
% 0.98/0.65    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.98/0.65    inference(cnf_transformation,[],[f36])).
% 0.98/0.65  fof(f36,plain,(
% 0.98/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.98/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f35])).
% 0.98/0.65  fof(f35,plain,(
% 0.98/0.65    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.98/0.65    introduced(choice_axiom,[])).
% 0.98/0.65  fof(f22,plain,(
% 0.98/0.65    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.98/0.65    inference(ennf_transformation,[],[f13])).
% 0.98/0.65  fof(f13,plain,(
% 0.98/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.98/0.65    inference(rectify,[],[f2])).
% 0.98/0.65  fof(f2,axiom,(
% 0.98/0.65    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.98/0.65  fof(f108,plain,(
% 0.98/0.65    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl5_1),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f74,f77,f64,f47])).
% 0.98/0.65  fof(f47,plain,(
% 0.98/0.65    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.98/0.65    inference(cnf_transformation,[],[f30])).
% 0.98/0.65  fof(f30,plain,(
% 0.98/0.65    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.98/0.65    inference(nnf_transformation,[],[f16])).
% 0.98/0.65  fof(f16,plain,(
% 0.98/0.65    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.98/0.65    inference(ennf_transformation,[],[f8])).
% 0.98/0.65  fof(f8,axiom,(
% 0.98/0.65    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.98/0.65  fof(f64,plain,(
% 0.98/0.65    r1_tsep_1(sK1,sK2) | ~spl5_1),
% 0.98/0.65    inference(avatar_component_clause,[],[f62])).
% 0.98/0.65  fof(f62,plain,(
% 0.98/0.65    spl5_1 <=> r1_tsep_1(sK1,sK2)),
% 0.98/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.98/0.65  fof(f77,plain,(
% 0.98/0.65    l1_struct_0(sK2)),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f72,f49])).
% 0.98/0.65  fof(f49,plain,(
% 0.98/0.65    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.98/0.65    inference(cnf_transformation,[],[f17])).
% 0.98/0.65  fof(f17,plain,(
% 0.98/0.65    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.98/0.65    inference(ennf_transformation,[],[f5])).
% 0.98/0.65  fof(f5,axiom,(
% 0.98/0.65    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.98/0.65  fof(f74,plain,(
% 0.98/0.65    l1_struct_0(sK1)),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f71,f49])).
% 0.98/0.65  fof(f71,plain,(
% 0.98/0.65    l1_pre_topc(sK1)),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f42,f40,f50])).
% 0.98/0.65  fof(f42,plain,(
% 0.98/0.65    m1_pre_topc(sK1,sK0)),
% 0.98/0.65    inference(cnf_transformation,[],[f29])).
% 0.98/0.65  fof(f83,plain,(
% 0.98/0.65    r2_hidden(sK3(u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f80,f54])).
% 0.98/0.65  fof(f54,plain,(
% 0.98/0.65    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.98/0.65    inference(cnf_transformation,[],[f34])).
% 0.98/0.65  fof(f34,plain,(
% 0.98/0.65    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.98/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 0.98/0.65  fof(f33,plain,(
% 0.98/0.65    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.98/0.65    introduced(choice_axiom,[])).
% 0.98/0.65  fof(f32,plain,(
% 0.98/0.65    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.98/0.65    inference(rectify,[],[f31])).
% 0.98/0.65  fof(f31,plain,(
% 0.98/0.65    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.98/0.65    inference(nnf_transformation,[],[f1])).
% 0.98/0.65  fof(f1,axiom,(
% 0.98/0.65    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.98/0.65  fof(f80,plain,(
% 0.98/0.65    ~v1_xboole_0(u1_struct_0(sK1))),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f41,f74,f52])).
% 0.98/0.65  fof(f52,plain,(
% 0.98/0.65    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.98/0.65    inference(cnf_transformation,[],[f21])).
% 0.98/0.65  fof(f21,plain,(
% 0.98/0.65    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.98/0.65    inference(flattening,[],[f20])).
% 0.98/0.65  fof(f20,plain,(
% 0.98/0.65    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.98/0.65    inference(ennf_transformation,[],[f7])).
% 0.98/0.65  fof(f7,axiom,(
% 0.98/0.65    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.98/0.65  fof(f41,plain,(
% 0.98/0.65    ~v2_struct_0(sK1)),
% 0.98/0.65    inference(cnf_transformation,[],[f29])).
% 0.98/0.65  fof(f100,plain,(
% 0.98/0.65    spl5_1 | ~spl5_2),
% 0.98/0.65    inference(avatar_contradiction_clause,[],[f98])).
% 0.98/0.65  fof(f98,plain,(
% 0.98/0.65    $false | (spl5_1 | ~spl5_2)),
% 0.98/0.65    inference(unit_resulting_resolution,[],[f77,f74,f63,f68,f58])).
% 0.98/0.65  fof(f58,plain,(
% 0.98/0.65    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.98/0.65    inference(cnf_transformation,[],[f25])).
% 0.98/0.65  fof(f25,plain,(
% 0.98/0.65    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.98/0.65    inference(flattening,[],[f24])).
% 0.98/0.65  fof(f24,plain,(
% 0.98/0.65    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.98/0.65    inference(ennf_transformation,[],[f9])).
% 0.98/0.65  fof(f9,axiom,(
% 0.98/0.65    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.98/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.98/0.65  fof(f68,plain,(
% 0.98/0.65    r1_tsep_1(sK2,sK1) | ~spl5_2),
% 0.98/0.65    inference(avatar_component_clause,[],[f66])).
% 0.98/0.65  fof(f66,plain,(
% 0.98/0.65    spl5_2 <=> r1_tsep_1(sK2,sK1)),
% 0.98/0.65    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.98/0.65  fof(f63,plain,(
% 0.98/0.65    ~r1_tsep_1(sK1,sK2) | spl5_1),
% 0.98/0.65    inference(avatar_component_clause,[],[f62])).
% 0.98/0.65  fof(f69,plain,(
% 0.98/0.65    spl5_1 | spl5_2),
% 0.98/0.65    inference(avatar_split_clause,[],[f46,f66,f62])).
% 0.98/0.65  fof(f46,plain,(
% 0.98/0.65    r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)),
% 0.98/0.65    inference(cnf_transformation,[],[f29])).
% 0.98/0.65  % SZS output end Proof for theBenchmark
% 0.98/0.65  % (14054)------------------------------
% 0.98/0.65  % (14054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.98/0.65  % (14054)Termination reason: Refutation
% 0.98/0.65  
% 0.98/0.65  % (14054)Memory used [KB]: 10618
% 0.98/0.65  % (14054)Time elapsed: 0.035 s
% 0.98/0.65  % (14054)------------------------------
% 0.98/0.65  % (14054)------------------------------
% 0.98/0.65  % (13879)Success in time 0.284 s
%------------------------------------------------------------------------------
