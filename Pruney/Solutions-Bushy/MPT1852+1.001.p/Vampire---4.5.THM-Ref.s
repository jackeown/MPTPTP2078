%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1852+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 177 expanded)
%              Number of leaves         :   18 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  258 ( 678 expanded)
%              Number of equality atoms :   28 (  85 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f73,f114,f119,f145,f173,f181,f187])).

% (20057)Termination reason: Refutation not found, incomplete strategy

% (20057)Memory used [KB]: 10618
% (20057)Time elapsed: 0.105 s
% (20057)------------------------------
% (20057)------------------------------
fof(f187,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f185,f167,f134,f52,f37,f178])).

fof(f178,plain,
    ( spl3_18
  <=> r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f37,plain,
    ( spl3_2
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,
    ( spl3_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f134,plain,
    ( spl3_14
  <=> r2_hidden(sK2(sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f167,plain,
    ( spl3_17
  <=> m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f185,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f54,f39,f136,f169,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
        & r2_hidden(sK2(X0),u1_pre_topc(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(f169,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f167])).

fof(f136,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f39,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f54,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f181,plain,
    ( ~ spl3_18
    | spl3_1
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f176,f116,f111,f47,f32,f178])).

fof(f32,plain,
    ( spl3_1
  <=> v3_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f47,plain,
    ( spl3_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f111,plain,
    ( spl3_11
  <=> u1_pre_topc(sK0) = u1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f116,plain,
    ( spl3_12
  <=> u1_struct_0(sK0) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f176,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f175,f113])).

fof(f113,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f175,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f174,f49])).

fof(f49,plain,
    ( l1_pre_topc(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f174,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | spl3_1
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f164,f34])).

fof(f34,plain,
    ( ~ v3_tdlat_3(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f164,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl3_12 ),
    inference(superposition,[],[f28,f118])).

fof(f118,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f28,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f173,plain,
    ( spl3_17
    | spl3_1
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f172,f116,f47,f32,f167])).

fof(f172,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f171,f49])).

fof(f171,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK1)
    | spl3_1
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f163,f34])).

fof(f163,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl3_12 ),
    inference(superposition,[],[f26,f118])).

fof(f26,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f145,plain,
    ( spl3_14
    | spl3_1
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f144,f111,f47,f32,f134])).

fof(f144,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f143,f49])).

fof(f143,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK1)
    | spl3_1
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f125,f34])).

fof(f125,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f27,f113])).

fof(f27,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f119,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f106,f70,f42,f116])).

fof(f42,plain,
    ( spl3_3
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f70,plain,
    ( spl3_6
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f106,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f44,f72,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f72,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f44,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f114,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f107,f70,f42,f111])).

fof(f107,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(sK1)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f44,f72,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f63,f47,f70])).

fof(f63,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f49,f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f52])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v3_tdlat_3(sK1)
    & v3_tdlat_3(sK0)
    & g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
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

fof(f13,plain,
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

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

% (20049)Termination reason: Refutation not found, incomplete strategy
fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

% (20049)Memory used [KB]: 10618
% (20049)Time elapsed: 0.107 s
fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).

% (20049)------------------------------
% (20049)------------------------------
fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f37])).

fof(f22,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f23,f32])).

fof(f23,plain,(
    ~ v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
