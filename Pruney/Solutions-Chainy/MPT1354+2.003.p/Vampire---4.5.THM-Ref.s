%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 209 expanded)
%              Number of leaves         :   13 (  66 expanded)
%              Depth                    :   14
%              Number of atoms          :  257 ( 966 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f43,f80,f83,f100,f106,f112,f118])).

fof(f118,plain,
    ( spl2_2
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl2_2
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f116,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v2_tops_2(sK1,sK0) )
    & ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | v2_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ v2_tops_2(X1,X0) )
            & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
              | v2_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ v2_tops_2(X1,sK0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | v2_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ v2_tops_2(X1,sK0) )
        & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | v2_tops_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ v2_tops_2(sK1,sK0) )
      & ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_tops_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ v2_tops_2(X1,X0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ v2_tops_2(X1,X0) )
          & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
            | v2_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_2(X1,X0)
          <~> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
            <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).

fof(f116,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_2
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f115,f74])).

fof(f74,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_5
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f115,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f114,f41])).

fof(f41,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_2
  <=> r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f114,plain,
    ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_6 ),
    inference(resolution,[],[f79,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k7_setfam_1(X0,X1),X2)
      | r1_tarski(X1,k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
              | ~ r1_tarski(X1,k7_setfam_1(X0,X2)) )
            & ( r1_tarski(X1,k7_setfam_1(X0,X2))
              | ~ r1_tarski(k7_setfam_1(X0,X1),X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).

fof(f79,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl2_6
  <=> r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f112,plain,
    ( spl2_6
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f110,f23])).

fof(f110,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f109,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f109,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_6
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f108,f105])).

fof(f105,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_7
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f108,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_6 ),
    inference(resolution,[],[f78,f46])).

fof(f46,plain,(
    ! [X2,X1] :
      ( r1_tarski(k7_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f78,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f106,plain,
    ( spl2_7
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f101,f35,f103])).

fof(f35,plain,
    ( spl2_1
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f101,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f64,f22])).

fof(f64,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f29,f23])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_tops_2(X1,X0)
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).

fof(f100,plain,
    ( spl2_1
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl2_1
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f98,f22])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f97,f23])).

fof(f97,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f96,f37])).

fof(f37,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f96,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f95,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f95,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f94,f23])).

fof(f94,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f91,f22])).

fof(f91,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_6 ),
    inference(resolution,[],[f60,f79])).

fof(f60,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k7_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
      | v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    inference(resolution,[],[f28,f31])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f81,f22])).

fof(f81,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_5 ),
    inference(resolution,[],[f75,f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f75,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f80,plain,
    ( ~ spl2_5
    | spl2_6
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f71,f39,f77,f73])).

fof(f71,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f70,f23])).

fof(f70,plain,
    ( r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_2 ),
    inference(resolution,[],[f33,f40])).

fof(f40,plain,
    ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
      | r1_tarski(k7_setfam_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f24,f39,f35])).

fof(f24,plain,
    ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f25,f39,f35])).

fof(f25,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:57:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (11681)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.47  % (11673)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.47  % (11673)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f42,f43,f80,f83,f100,f106,f112,f118])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    spl2_2 | ~spl2_5 | ~spl2_6),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f117])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    $false | (spl2_2 | ~spl2_5 | ~spl2_6)),
% 0.22/0.47    inference(subsumption_resolution,[],[f116,f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ((~r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_tops_2(sK1,sK0)) & (r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((~r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_tops_2(X1,X0)) & (r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | v2_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_tops_2(X1,sK0)) & (r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X1] : ((~r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_tops_2(X1,sK0)) & (r1_tarski(X1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => ((~r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_tops_2(sK1,sK0)) & (r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((~r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_tops_2(X1,X0)) & (r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | v2_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (((~r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_tops_2(X1,X0)) & (r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | v2_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((v2_tops_2(X1,X0) <~> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f6])).
% 0.22/0.47  fof(f6,conjecture,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl2_2 | ~spl2_5 | ~spl2_6)),
% 0.22/0.47    inference(subsumption_resolution,[],[f115,f74])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    spl2_5 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl2_2 | ~spl2_6)),
% 0.22/0.47    inference(subsumption_resolution,[],[f114,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ~r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f39])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    spl2_2 <=> r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_6),
% 0.22/0.47    inference(resolution,[],[f79,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k7_setfam_1(X0,X1),X2) | r1_tarski(X1,k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (((r1_tarski(k7_setfam_1(X0,X1),X2) | ~r1_tarski(X1,k7_setfam_1(X0,X2))) & (r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.47    inference(nnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) | ~spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f77])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl2_6 <=> r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    spl2_6 | ~spl2_7),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f111])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    $false | (spl2_6 | ~spl2_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f110,f23])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl2_6 | ~spl2_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f109,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    l1_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl2_6 | ~spl2_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f108,f105])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f103])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    spl2_7 <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl2_6),
% 0.22/0.47    inference(resolution,[],[f78,f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X2,X1] : (r1_tarski(k7_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) )),
% 0.22/0.47    inference(resolution,[],[f27,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0) | r1_tarski(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) | spl2_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f77])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    spl2_7 | ~spl2_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f101,f35,f103])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl2_1 <=> v2_tops_2(sK1,sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    ~v2_tops_2(sK1,sK0) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f64,f22])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ~v2_tops_2(sK1,sK0) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.47    inference(resolution,[],[f29,f23])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0) | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & (v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tops_2)).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    spl2_1 | ~spl2_6),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f99])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    $false | (spl2_1 | ~spl2_6)),
% 0.22/0.47    inference(subsumption_resolution,[],[f98,f22])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_6)),
% 0.22/0.47    inference(subsumption_resolution,[],[f97,f23])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_6)),
% 0.22/0.47    inference(subsumption_resolution,[],[f96,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ~v2_tops_2(sK1,sK0) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f35])).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    v2_tops_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~spl2_6),
% 0.22/0.47    inference(resolution,[],[f95,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_6),
% 0.22/0.47    inference(subsumption_resolution,[],[f94,f23])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_6),
% 0.22/0.47    inference(subsumption_resolution,[],[f91,f22])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_6),
% 0.22/0.47    inference(resolution,[],[f60,f79])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X2,X1] : (~r1_tarski(k7_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) | v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) )),
% 0.22/0.48    inference(resolution,[],[f28,f31])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl2_5),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    $false | spl2_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f81,f22])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | spl2_5),
% 0.22/0.48    inference(resolution,[],[f75,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl2_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f73])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ~spl2_5 | spl2_6 | ~spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f71,f39,f77,f73])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f70,f23])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_2),
% 0.22/0.48    inference(resolution,[],[f33,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f39])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X1,k7_setfam_1(X0,X2)) | r1_tarski(k7_setfam_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl2_1 | spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f39,f35])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ~spl2_1 | ~spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f39,f35])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_tops_2(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (11673)------------------------------
% 0.22/0.48  % (11673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (11673)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (11673)Memory used [KB]: 5373
% 0.22/0.48  % (11673)Time elapsed: 0.064 s
% 0.22/0.48  % (11673)------------------------------
% 0.22/0.48  % (11673)------------------------------
% 0.22/0.48  % (11665)Success in time 0.118 s
%------------------------------------------------------------------------------
