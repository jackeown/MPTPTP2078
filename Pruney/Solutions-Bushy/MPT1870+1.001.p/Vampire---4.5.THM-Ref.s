%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1870+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 433 expanded)
%              Number of leaves         :   19 ( 175 expanded)
%              Depth                    :   11
%              Number of atoms          :  493 (3949 expanded)
%              Number of equality atoms :   10 (  29 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f139,f146,f152,f213,f293,f295,f297,f299])).

fof(f299,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f30,f284])).

fof(f284,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl5_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v2_tex_2(sK2,sK0)
    & v2_tex_2(sK1,sK0)
    & v3_pre_topc(sK2,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v2_tex_2(X2,X0)
                & v2_tex_2(X1,X0)
                & v3_pre_topc(X2,X0)
                & v3_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v2_tex_2(X2,sK0)
              & v2_tex_2(X1,sK0)
              & v3_pre_topc(X2,sK0)
              & v3_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v2_tex_2(X2,sK0)
            & v2_tex_2(X1,sK0)
            & v3_pre_topc(X2,sK0)
            & v3_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v2_tex_2(X2,sK0)
          & v2_tex_2(sK1,sK0)
          & v3_pre_topc(X2,sK0)
          & v3_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v2_tex_2(X2,sK0)
        & v2_tex_2(sK1,sK0)
        & v3_pre_topc(X2,sK0)
        & v3_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v2_tex_2(sK2,sK0)
      & v2_tex_2(sK1,sK0)
      & v3_pre_topc(sK2,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v2_tex_2(X2,X0)
              & v2_tex_2(X1,X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  & v2_tex_2(X1,X0)
                  & v3_pre_topc(X2,X0)
                  & v3_pre_topc(X1,X0) )
               => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tex_2)).

fof(f297,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_11 ),
    inference(subsumption_resolution,[],[f242,f288])).

fof(f288,plain,
    ( ~ v3_pre_topc(k3_xboole_0(sK3(sK0),sK4(sK0)),sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl5_11
  <=> v3_pre_topc(k3_xboole_0(sK3(sK0),sK4(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f242,plain,
    ( v3_pre_topc(k3_xboole_0(sK3(sK0),sK4(sK0)),sK0)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f29,f30,f82,f151,f145,f212,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f212,plain,
    ( m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl5_7
  <=> m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f145,plain,
    ( v3_pre_topc(sK4(sK0),sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl5_3
  <=> v3_pre_topc(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f151,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_4
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f82,plain,
    ( v3_pre_topc(sK3(sK0),sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl5_1
  <=> v3_pre_topc(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f295,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7
    | spl5_12 ),
    inference(subsumption_resolution,[],[f250,f292])).

fof(f292,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK3(sK0),sK4(sK0)),sK0)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl5_12
  <=> v3_pre_topc(k2_xboole_0(sK3(sK0),sK4(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f250,plain,
    ( v3_pre_topc(k2_xboole_0(sK3(sK0),sK4(sK0)),sK0)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f29,f30,f82,f151,f145,f212,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f293,plain,
    ( ~ spl5_10
    | spl5_2
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f280,f210,f149,f290,f286,f84,f282])).

fof(f84,plain,
    ( spl5_2
  <=> ! [X1,X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v2_tex_2(X1,sK0)
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X0),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k2_xboole_0(sK3(sK0),sK4(sK0)),sK0)
        | ~ v3_pre_topc(k3_xboole_0(sK3(sK0),sK4(sK0)),sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ v2_tex_2(X1,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X0),sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f279,f254])).

fof(f254,plain,
    ( k2_xboole_0(sK3(sK0),sK4(sK0)) = k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0))
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f151,f212,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f279,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(k3_xboole_0(sK3(sK0),sK4(sK0)),sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ v2_tex_2(X1,sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(k4_subset_1(u1_struct_0(sK0),sK3(sK0),sK4(sK0)),sK0)
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X0),sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_7 ),
    inference(superposition,[],[f42,f260])).

fof(f260,plain,
    ( ! [X0] : k3_xboole_0(X0,sK4(sK0)) = k9_subset_1(u1_struct_0(sK0),X0,sK4(sK0))
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f212,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
          | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) )
        & v3_pre_topc(sK4(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f24,f26,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
                | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
              & v3_pre_topc(X4,X0)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X4] :
            ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),X4),X0)
              | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),X4),X0) )
            & v3_pre_topc(X4,X0)
            & v3_pre_topc(sK3(X0),X0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X4] :
          ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),X4),X0)
            | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),X4),X0) )
          & v3_pre_topc(X4,X0)
          & v3_pre_topc(sK3(X0),X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0)
          | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK3(X0),sK4(X0)),X0) )
        & v3_pre_topc(sK4(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X3] :
          ( ? [X4] :
              ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
                | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X3,X4),X0) )
              & v3_pre_topc(X4,X0)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ! [X4] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              | ~ v2_tex_2(X4,X0)
              | ~ v2_tex_2(X3,X0)
              | ~ v3_pre_topc(X4,X0)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X3] :
          ( ! [X4] :
              ( v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              | ~ v2_tex_2(X4,X0)
              | ~ v2_tex_2(X3,X0)
              | ~ v3_pre_topc(X4,X0)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      | ? [X1] :
          ( ? [X2] :
              ( ( ~ v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => ( v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X3] :
            ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X4] :
                ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X4,X0)
                    & v2_tex_2(X3,X0)
                    & v3_pre_topc(X4,X0)
                    & v3_pre_topc(X3,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => ( v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    & v2_tex_2(X1,X0)
                    & v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tex_2)).

fof(f213,plain,
    ( spl5_7
    | spl5_2 ),
    inference(avatar_split_clause,[],[f208,f84,f210])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK4(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X0),sK0) ) ),
    inference(resolution,[],[f39,f30])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f152,plain,
    ( spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f147,f84,f149])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X0),sK0) ) ),
    inference(resolution,[],[f38,f30])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,
    ( spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f109,f84,f143])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ v3_pre_topc(X0,sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK4(sK0),sK0)
      | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X0),sK0) ) ),
    inference(resolution,[],[f41,f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK4(X0),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f139,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f57,f137])).

fof(f137,plain,
    ( v2_tex_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f132,f53])).

fof(f53,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f31,f32,f46])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f132,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f33,f34,f35,f36,f31,f32,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | v2_tex_2(k4_subset_1(u1_struct_0(sK0),X1,X0),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f36,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ~ v2_tex_2(k2_xboole_0(sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f37,f53])).

fof(f37,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f57,f92])).

fof(f92,plain,
    ( v2_tex_2(k2_xboole_0(sK1,sK2),sK0)
    | spl5_1 ),
    inference(forward_demodulation,[],[f89,f53])).

fof(f89,plain,
    ( v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f30,f36,f34,f35,f33,f31,f32,f81,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X2,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK3(X0),X0)
      | v2_tex_2(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,
    ( ~ v3_pre_topc(sK3(sK0),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f80])).

%------------------------------------------------------------------------------
