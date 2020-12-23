%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 895 expanded)
%              Number of leaves         :   26 ( 276 expanded)
%              Depth                    :   21
%              Number of atoms          :  460 (4078 expanded)
%              Number of equality atoms :   26 ( 633 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f467,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f231,f261,f274,f282,f296,f304,f398,f404,f409,f462])).

fof(f462,plain,
    ( ~ spl3_11
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f461])).

fof(f461,plain,
    ( $false
    | ~ spl3_11
    | ~ spl3_27 ),
    inference(global_subsumption,[],[f236,f460,f434])).

fof(f434,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ spl3_27 ),
    inference(superposition,[],[f87,f408])).

fof(f408,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl3_27
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f87,plain,(
    r2_hidden(sK2(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f86,f49])).

fof(f49,plain,(
    ~ v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ v3_tdlat_3(sK1)
    & v3_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tdlat_3(X1)
            & v3_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(sK0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ~ v3_tdlat_3(X1)
        & v3_tdlat_3(sK0)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        & l1_pre_topc(X1) )
   => ( ~ v3_tdlat_3(sK1)
      & v3_tdlat_3(sK0)
      & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).

fof(f86,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK1))
    | v3_tdlat_3(sK1) ),
    inference(resolution,[],[f55,f46])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
            & r2_hidden(sK2(X0),u1_pre_topc(X0))
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
        & r2_hidden(sK2(X0),u1_pre_topc(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(f460,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ spl3_11
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f459,f230])).

fof(f230,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl3_11
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f459,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0))
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f458,f46])).

fof(f458,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f447,f49])).

fof(f447,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0))
    | v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl3_27 ),
    inference(superposition,[],[f56,f408])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f236,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f235,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f235,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f232,f48])).

fof(f48,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f232,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ v3_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f215,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f215,plain,(
    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f209,f45])).

fof(f209,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f186,f105])).

fof(f105,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK1,X0)
      | m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f91,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f91,plain,(
    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f90,f49])).

fof(f90,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_tdlat_3(sK1) ),
    inference(resolution,[],[f54,f46])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f186,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f185,f46])).

fof(f185,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f180,f45])).

fof(f180,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f102,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f102,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f101,f47])).

fof(f47,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f98,f46])).

fof(f98,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f57,f77])).

fof(f77,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f50,f46])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f409,plain,
    ( ~ spl3_21
    | spl3_27
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f399,f277,f406,f299])).

fof(f299,plain,
    ( spl3_21
  <=> r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f277,plain,
    ( spl3_18
  <=> r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f399,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ spl3_18 ),
    inference(resolution,[],[f278,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f278,plain,
    ( r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f277])).

fof(f404,plain,(
    ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f402,f157])).

fof(f157,plain,(
    m1_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f100,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f94,f46])).

fof(f94,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1) ) ),
    inference(superposition,[],[f66,f47])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f100,plain,(
    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f99,f45])).

fof(f99,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f76])).

fof(f76,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f50,f45])).

fof(f402,plain,
    ( ~ m1_pre_topc(sK0,sK1)
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f401,f46])).

fof(f401,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(sK0,sK1)
    | ~ spl3_19 ),
    inference(resolution,[],[f291,f79])).

fof(f79,plain,(
    v1_tops_2(u1_pre_topc(sK1),sK1) ),
    inference(resolution,[],[f51,f46])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v1_tops_2(u1_pre_topc(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_tops_2(u1_pre_topc(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).

fof(f291,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(u1_pre_topc(sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl3_19
  <=> ! [X0] :
        ( ~ v1_tops_2(u1_pre_topc(sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f398,plain,(
    ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f397])).

fof(f397,plain,
    ( $false
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f396,f186])).

fof(f396,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f395,f45])).

fof(f395,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl3_16 ),
    inference(resolution,[],[f269,f78])).

fof(f78,plain,(
    v1_tops_2(u1_pre_topc(sK0),sK0) ),
    inference(resolution,[],[f51,f45])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl3_16
  <=> ! [X0] :
        ( ~ v1_tops_2(u1_pre_topc(sK0),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f304,plain,
    ( spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f303,f293,f299])).

fof(f293,plain,
    ( spl3_20
  <=> v1_tops_2(u1_pre_topc(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f303,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f287,f45])).

fof(f287,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK1),sK0)
    | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f214,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f214,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f208,f45])).

fof(f208,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f186,f113])).

fof(f113,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK1,X1)
      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f83,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).

fof(f83,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(resolution,[],[f52,f46])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f296,plain,
    ( spl3_19
    | spl3_20 ),
    inference(avatar_split_clause,[],[f284,f293,f290])).

fof(f284,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(sK1),sK0)
      | ~ v1_tops_2(u1_pre_topc(sK1),X0)
      | ~ m1_pre_topc(sK0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f214,f75])).

fof(f75,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | v1_tops_2(X3,X2)
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f72,f62])).

fof(f72,plain,(
    ! [X2,X0,X3] :
      ( v1_tops_2(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_tops_2(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v1_tops_2(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              | ~ v1_tops_2(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

fof(f282,plain,
    ( spl3_18
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f281,f271,f277])).

fof(f271,plain,
    ( spl3_17
  <=> v1_tops_2(u1_pre_topc(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f281,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f265,f46])).

fof(f265,plain,
    ( ~ v1_tops_2(u1_pre_topc(sK0),sK1)
    | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f199,f63])).

fof(f199,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f198,f46])).

fof(f198,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f108,f157])).

fof(f108,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(sK0,X1)
      | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f82,f62])).

fof(f82,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f52,f45])).

fof(f274,plain,
    ( spl3_16
    | spl3_17 ),
    inference(avatar_split_clause,[],[f262,f271,f268])).

fof(f262,plain,(
    ! [X0] :
      ( v1_tops_2(u1_pre_topc(sK0),sK1)
      | ~ v1_tops_2(u1_pre_topc(sK0),X0)
      | ~ m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f199,f75])).

fof(f261,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | spl3_10 ),
    inference(subsumption_resolution,[],[f248,f226])).

fof(f226,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl3_10
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f248,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f217,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f217,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f212,f45])).

fof(f212,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f186,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f231,plain,
    ( ~ spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f221,f228,f224])).

fof(f221,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f220,f69])).

fof(f220,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f195,f70])).

fof(f195,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f190,f46])).

fof(f190,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f157,f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:14:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (9911)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (9925)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (9910)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (9917)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.50  % (9915)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (9920)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (9916)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (9919)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (9910)Refutation not found, incomplete strategy% (9910)------------------------------
% 0.22/0.51  % (9910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9917)Refutation not found, incomplete strategy% (9917)------------------------------
% 0.22/0.51  % (9917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9917)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9917)Memory used [KB]: 1663
% 0.22/0.51  % (9917)Time elapsed: 0.058 s
% 0.22/0.51  % (9917)------------------------------
% 0.22/0.51  % (9917)------------------------------
% 0.22/0.51  % (9910)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9910)Memory used [KB]: 10618
% 0.22/0.51  % (9910)Time elapsed: 0.058 s
% 0.22/0.51  % (9910)------------------------------
% 0.22/0.51  % (9910)------------------------------
% 0.22/0.51  % (9912)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (9933)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (9927)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (9914)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (9932)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (9920)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f467,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f231,f261,f274,f282,f296,f304,f398,f404,f409,f462])).
% 0.22/0.51  fof(f462,plain,(
% 0.22/0.51    ~spl3_11 | ~spl3_27),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f461])).
% 0.22/0.51  fof(f461,plain,(
% 0.22/0.51    $false | (~spl3_11 | ~spl3_27)),
% 0.22/0.51    inference(global_subsumption,[],[f236,f460,f434])).
% 0.22/0.51  fof(f434,plain,(
% 0.22/0.51    r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~spl3_27),
% 0.22/0.51    inference(superposition,[],[f87,f408])).
% 0.22/0.51  fof(f408,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~spl3_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f406])).
% 0.22/0.51  fof(f406,plain,(
% 0.22/0.51    spl3_27 <=> u1_pre_topc(sK0) = u1_pre_topc(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    r2_hidden(sK2(sK1),u1_pre_topc(sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f86,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ~v3_tdlat_3(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    (~v3_tdlat_3(sK1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1)) & l1_pre_topc(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f34,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) & l1_pre_topc(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) & l1_pre_topc(X1)) => (~v3_tdlat_3(sK1) & v3_tdlat_3(sK0) & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) & l1_pre_topc(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 0.22/0.51    inference(negated_conjecture,[],[f15])).
% 0.22/0.51  fof(f15,conjecture,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tex_2)).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    r2_hidden(sK2(sK1),u1_pre_topc(sK1)) | v3_tdlat_3(sK1)),
% 0.22/0.51    inference(resolution,[],[f55,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    l1_pre_topc(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | r2_hidden(sK2(X0),u1_pre_topc(X0)) | v3_tdlat_3(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0] : (((v3_tdlat_3(X0) | (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(rectify,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tdlat_3)).
% 0.22/0.51  fof(f460,plain,(
% 0.22/0.51    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | (~spl3_11 | ~spl3_27)),
% 0.22/0.51    inference(forward_demodulation,[],[f459,f230])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    u1_struct_0(sK0) = u1_struct_0(sK1) | ~spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f228])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    spl3_11 <=> u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.51  fof(f459,plain,(
% 0.22/0.51    ~r2_hidden(k6_subset_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0)) | ~spl3_27),
% 0.22/0.51    inference(subsumption_resolution,[],[f458,f46])).
% 0.22/0.51  fof(f458,plain,(
% 0.22/0.51    ~r2_hidden(k6_subset_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0)) | ~l1_pre_topc(sK1) | ~spl3_27),
% 0.22/0.51    inference(subsumption_resolution,[],[f447,f49])).
% 0.22/0.51  fof(f447,plain,(
% 0.22/0.51    ~r2_hidden(k6_subset_1(u1_struct_0(sK1),sK2(sK1)),u1_pre_topc(sK0)) | v3_tdlat_3(sK1) | ~l1_pre_topc(sK1) | ~spl3_27),
% 0.22/0.51    inference(superposition,[],[f56,f408])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) | v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f235,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f232,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    v3_tdlat_3(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f215,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,u1_pre_topc(X0)) | r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f209,f45])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.51    inference(resolution,[],[f186,f105])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_pre_topc(sK1,X0) | m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(resolution,[],[f91,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f90,f49])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | v3_tdlat_3(sK1)),
% 0.22/0.51    inference(resolution,[],[f54,f46])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | v3_tdlat_3(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f185,f46])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f180,f45])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1)),
% 0.22/0.51    inference(resolution,[],[f102,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f101,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f98,f46])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f97])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK1)),
% 0.22/0.51    inference(resolution,[],[f57,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK1)),
% 0.22/0.51    inference(resolution,[],[f50,f46])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f409,plain,(
% 0.22/0.52    ~spl3_21 | spl3_27 | ~spl3_18),
% 0.22/0.52    inference(avatar_split_clause,[],[f399,f277,f406,f299])).
% 0.22/0.52  fof(f299,plain,(
% 0.22/0.52    spl3_21 <=> r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.52  fof(f277,plain,(
% 0.22/0.52    spl3_18 <=> r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.52  fof(f399,plain,(
% 0.22/0.52    u1_pre_topc(sK0) = u1_pre_topc(sK1) | ~r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~spl3_18),
% 0.22/0.52    inference(resolution,[],[f278,f69])).
% 0.22/0.52  fof(f69,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f278,plain,(
% 0.22/0.52    r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~spl3_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f277])).
% 0.22/0.52  fof(f404,plain,(
% 0.22/0.52    ~spl3_19),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f403])).
% 0.22/0.52  fof(f403,plain,(
% 0.22/0.52    $false | ~spl3_19),
% 0.22/0.52    inference(subsumption_resolution,[],[f402,f157])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    m1_pre_topc(sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f100,f95])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f94,f46])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | m1_pre_topc(X0,sK1) | ~l1_pre_topc(sK1)) )),
% 0.22/0.52    inference(superposition,[],[f66,f47])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f99,f45])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f96])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f57,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    m1_pre_topc(sK0,sK0)),
% 0.22/0.52    inference(resolution,[],[f50,f45])).
% 0.22/0.52  fof(f402,plain,(
% 0.22/0.52    ~m1_pre_topc(sK0,sK1) | ~spl3_19),
% 0.22/0.52    inference(subsumption_resolution,[],[f401,f46])).
% 0.22/0.52  fof(f401,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | ~m1_pre_topc(sK0,sK1) | ~spl3_19),
% 0.22/0.52    inference(resolution,[],[f291,f79])).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    v1_tops_2(u1_pre_topc(sK1),sK1)),
% 0.22/0.52    inference(resolution,[],[f51,f46])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | v1_tops_2(u1_pre_topc(X0),X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (v1_tops_2(u1_pre_topc(X0),X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => v1_tops_2(u1_pre_topc(X0),X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_compts_1)).
% 0.22/0.52  fof(f291,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_tops_2(u1_pre_topc(sK1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0)) ) | ~spl3_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f290])).
% 0.22/0.52  fof(f290,plain,(
% 0.22/0.52    spl3_19 <=> ! [X0] : (~v1_tops_2(u1_pre_topc(sK1),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK0,X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.52  fof(f398,plain,(
% 0.22/0.52    ~spl3_16),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f397])).
% 0.22/0.52  fof(f397,plain,(
% 0.22/0.52    $false | ~spl3_16),
% 0.22/0.52    inference(subsumption_resolution,[],[f396,f186])).
% 0.22/0.52  fof(f396,plain,(
% 0.22/0.52    ~m1_pre_topc(sK1,sK0) | ~spl3_16),
% 0.22/0.52    inference(subsumption_resolution,[],[f395,f45])).
% 0.22/0.52  fof(f395,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~spl3_16),
% 0.22/0.52    inference(resolution,[],[f269,f78])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    v1_tops_2(u1_pre_topc(sK0),sK0)),
% 0.22/0.52    inference(resolution,[],[f51,f45])).
% 0.22/0.52  fof(f269,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_tops_2(u1_pre_topc(sK0),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0)) ) | ~spl3_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f268])).
% 0.22/0.52  fof(f268,plain,(
% 0.22/0.52    spl3_16 <=> ! [X0] : (~v1_tops_2(u1_pre_topc(sK0),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.52  fof(f304,plain,(
% 0.22/0.52    spl3_21 | ~spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f303,f293,f299])).
% 0.22/0.52  fof(f293,plain,(
% 0.22/0.52    spl3_20 <=> v1_tops_2(u1_pre_topc(sK1),sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.52  fof(f303,plain,(
% 0.22/0.52    ~v1_tops_2(u1_pre_topc(sK1),sK0) | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0))),
% 0.22/0.52    inference(subsumption_resolution,[],[f287,f45])).
% 0.22/0.52  fof(f287,plain,(
% 0.22/0.52    ~v1_tops_2(u1_pre_topc(sK1),sK0) | r1_tarski(u1_pre_topc(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f214,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0) | r1_tarski(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    inference(subsumption_resolution,[],[f208,f45])).
% 0.22/0.52  fof(f208,plain,(
% 0.22/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f186,f113])).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_pre_topc(sK1,X1) | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~l1_pre_topc(X1)) )),
% 0.22/0.52    inference(resolution,[],[f83,f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) => m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_2)).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.52    inference(resolution,[],[f52,f46])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.52  fof(f296,plain,(
% 0.22/0.52    spl3_19 | spl3_20),
% 0.22/0.52    inference(avatar_split_clause,[],[f284,f293,f290])).
% 0.22/0.52  fof(f284,plain,(
% 0.22/0.52    ( ! [X0] : (v1_tops_2(u1_pre_topc(sK1),sK0) | ~v1_tops_2(u1_pre_topc(sK1),X0) | ~m1_pre_topc(sK0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(resolution,[],[f214,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | v1_tops_2(X3,X2) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f72,f62])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X2,X0,X3] : (v1_tops_2(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v1_tops_2(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v1_tops_2(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) | ~v1_tops_2(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).
% 0.22/0.52  fof(f282,plain,(
% 0.22/0.52    spl3_18 | ~spl3_17),
% 0.22/0.52    inference(avatar_split_clause,[],[f281,f271,f277])).
% 0.22/0.52  fof(f271,plain,(
% 0.22/0.52    spl3_17 <=> v1_tops_2(u1_pre_topc(sK0),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.52  fof(f281,plain,(
% 0.22/0.52    ~v1_tops_2(u1_pre_topc(sK0),sK1) | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f265,f46])).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    ~v1_tops_2(u1_pre_topc(sK0),sK1) | r1_tarski(u1_pre_topc(sK0),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)),
% 0.22/0.52    inference(resolution,[],[f199,f63])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.22/0.52    inference(subsumption_resolution,[],[f198,f46])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | ~l1_pre_topc(sK1)),
% 0.22/0.52    inference(resolution,[],[f108,f157])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_pre_topc(sK0,X1) | m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) | ~l1_pre_topc(X1)) )),
% 0.22/0.52    inference(resolution,[],[f82,f62])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    inference(resolution,[],[f52,f45])).
% 0.22/0.52  fof(f274,plain,(
% 0.22/0.52    spl3_16 | spl3_17),
% 0.22/0.52    inference(avatar_split_clause,[],[f262,f271,f268])).
% 0.22/0.52  fof(f262,plain,(
% 0.22/0.52    ( ! [X0] : (v1_tops_2(u1_pre_topc(sK0),sK1) | ~v1_tops_2(u1_pre_topc(sK0),X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(resolution,[],[f199,f75])).
% 0.22/0.52  fof(f261,plain,(
% 0.22/0.52    spl3_10),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f260])).
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    $false | spl3_10),
% 0.22/0.52    inference(subsumption_resolution,[],[f248,f226])).
% 0.22/0.52  fof(f226,plain,(
% 0.22/0.52    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | spl3_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f224])).
% 0.22/0.52  fof(f224,plain,(
% 0.22/0.52    spl3_10 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.52  fof(f248,plain,(
% 0.22/0.52    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.52    inference(resolution,[],[f217,f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f217,plain,(
% 0.22/0.52    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f212,f45])).
% 0.22/0.52  fof(f212,plain,(
% 0.22/0.52    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.52    inference(resolution,[],[f186,f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.52  fof(f231,plain,(
% 0.22/0.52    ~spl3_10 | spl3_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f221,f228,f224])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    u1_struct_0(sK0) = u1_struct_0(sK1) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.52    inference(resolution,[],[f220,f69])).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.52    inference(resolution,[],[f195,f70])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f190,f46])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.52    inference(resolution,[],[f157,f60])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (9920)------------------------------
% 0.22/0.52  % (9920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9920)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (9920)Memory used [KB]: 10874
% 0.22/0.52  % (9920)Time elapsed: 0.092 s
% 0.22/0.52  % (9920)------------------------------
% 0.22/0.52  % (9920)------------------------------
% 0.22/0.52  % (9909)Success in time 0.15 s
%------------------------------------------------------------------------------
