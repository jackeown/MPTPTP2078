%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t30_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:30 EDT 2019

% Result     : Theorem 34.62s
% Output     : Refutation 34.62s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 726 expanded)
%              Number of leaves         :   28 ( 222 expanded)
%              Depth                    :   24
%              Number of atoms          :  817 (2674 expanded)
%              Number of equality atoms :   66 ( 294 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22532,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f335,f350,f357,f364,f371,f378,f385,f407,f425,f2224,f2775,f3472,f19046,f22518,f22531])).

fof(f22531,plain,
    ( spl29_19
    | ~ spl29_118
    | ~ spl29_214
    | ~ spl29_746 ),
    inference(avatar_contradiction_clause,[],[f22530])).

fof(f22530,plain,
    ( $false
    | ~ spl29_19
    | ~ spl29_118
    | ~ spl29_214
    | ~ spl29_746 ),
    inference(subsumption_resolution,[],[f22529,f2214])).

fof(f2214,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_118 ),
    inference(avatar_component_clause,[],[f2213])).

fof(f2213,plain,
    ( spl29_118
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_118])])).

fof(f22529,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_19
    | ~ spl29_214
    | ~ spl29_746 ),
    inference(subsumption_resolution,[],[f22523,f3471])).

fof(f3471,plain,
    ( k3_xboole_0(k2_xboole_0(sK1,sK2),sK7(sK0,k2_xboole_0(sK1,sK2))) = sK7(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl29_214 ),
    inference(avatar_component_clause,[],[f3470])).

fof(f3470,plain,
    ( spl29_214
  <=> k3_xboole_0(k2_xboole_0(sK1,sK2),sK7(sK0,k2_xboole_0(sK1,sK2))) = sK7(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_214])])).

fof(f22523,plain,
    ( k3_xboole_0(k2_xboole_0(sK1,sK2),sK7(sK0,k2_xboole_0(sK1,sK2))) != sK7(sK0,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_19
    | ~ spl29_746 ),
    inference(resolution,[],[f19045,f424])).

fof(f424,plain,
    ( ~ v2_tex_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl29_19 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl29_19
  <=> ~ v2_tex_2(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_19])])).

fof(f19045,plain,
    ( ! [X2] :
        ( v2_tex_2(X2,sK0)
        | k3_xboole_0(X2,sK7(sK0,k2_xboole_0(sK1,sK2))) != sK7(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_746 ),
    inference(avatar_component_clause,[],[f19044])).

fof(f19044,plain,
    ( spl29_746
  <=> ! [X2] :
        ( k3_xboole_0(X2,sK7(sK0,k2_xboole_0(sK1,sK2))) != sK7(sK0,X2)
        | v2_tex_2(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_746])])).

fof(f22518,plain,
    ( spl29_744
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_4
    | ~ spl29_6
    | ~ spl29_8
    | ~ spl29_10
    | ~ spl29_12
    | ~ spl29_120
    | ~ spl29_214 ),
    inference(avatar_split_clause,[],[f22512,f3470,f2222,f383,f376,f369,f362,f355,f348,f333,f19038])).

fof(f19038,plain,
    ( spl29_744
  <=> v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_744])])).

fof(f333,plain,
    ( spl29_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_0])])).

fof(f348,plain,
    ( spl29_2
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_2])])).

fof(f355,plain,
    ( spl29_4
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_4])])).

fof(f362,plain,
    ( spl29_6
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_6])])).

fof(f369,plain,
    ( spl29_8
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_8])])).

fof(f376,plain,
    ( spl29_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_10])])).

fof(f383,plain,
    ( spl29_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_12])])).

fof(f2222,plain,
    ( spl29_120
  <=> m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_120])])).

fof(f22512,plain,
    ( v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_4
    | ~ spl29_6
    | ~ spl29_8
    | ~ spl29_10
    | ~ spl29_12
    | ~ spl29_120
    | ~ spl29_214 ),
    inference(subsumption_resolution,[],[f22511,f6450])).

fof(f6450,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK7(sK0,k2_xboole_0(sK1,sK2)),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_120 ),
    inference(superposition,[],[f4367,f274])).

fof(f274,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',commutativity_k3_xboole_0)).

fof(f4367,plain,
    ( ! [X4] : m1_subset_1(k3_xboole_0(X4,sK7(sK0,k2_xboole_0(sK1,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_120 ),
    inference(forward_demodulation,[],[f4366,f4358])).

fof(f4358,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),sK7(sK0,k2_xboole_0(sK1,sK2)),X1) = k3_xboole_0(X1,sK7(sK0,k2_xboole_0(sK1,sK2)))
    | ~ spl29_120 ),
    inference(subsumption_resolution,[],[f4332,f2223])).

fof(f2223,plain,
    ( m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_120 ),
    inference(avatar_component_clause,[],[f2222])).

fof(f4332,plain,
    ( ! [X1] :
        ( k9_subset_1(u1_struct_0(sK0),sK7(sK0,k2_xboole_0(sK1,sK2)),X1) = k3_xboole_0(X1,sK7(sK0,k2_xboole_0(sK1,sK2)))
        | ~ m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_120 ),
    inference(superposition,[],[f2613,f291])).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f178])).

fof(f178,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',redefinition_k9_subset_1)).

fof(f2613,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK7(sK0,k2_xboole_0(sK1,sK2))) = k9_subset_1(u1_struct_0(sK0),sK7(sK0,k2_xboole_0(sK1,sK2)),X1)
    | ~ spl29_120 ),
    inference(resolution,[],[f2223,f292])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f179])).

fof(f179,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',commutativity_k9_subset_1)).

fof(f4366,plain,
    ( ! [X4] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK7(sK0,k2_xboole_0(sK1,sK2)),X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_120 ),
    inference(subsumption_resolution,[],[f4345,f2223])).

fof(f4345,plain,
    ( ! [X4] :
        ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK7(sK0,k2_xboole_0(sK1,sK2)),X4),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_120 ),
    inference(superposition,[],[f290,f2613])).

fof(f290,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f177])).

fof(f177,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',dt_k9_subset_1)).

fof(f22511,plain,
    ( v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK7(sK0,k2_xboole_0(sK1,sK2)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_4
    | ~ spl29_6
    | ~ spl29_8
    | ~ spl29_10
    | ~ spl29_12
    | ~ spl29_120
    | ~ spl29_214 ),
    inference(subsumption_resolution,[],[f22510,f7046])).

fof(f7046,plain,
    ( ! [X1] : v3_pre_topc(k3_xboole_0(X1,sK2),sK0)
    | ~ spl29_0
    | ~ spl29_4
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(superposition,[],[f7038,f2906])).

fof(f2906,plain,
    ( ! [X1] : k3_xboole_0(X1,sK2) = k3_xboole_0(sK2,sK8(sK0,sK2,k3_xboole_0(X1,sK2)))
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(superposition,[],[f2257,f274])).

fof(f2257,plain,
    ( ! [X0] : k3_xboole_0(sK2,X0) = k3_xboole_0(sK2,sK8(sK0,sK2,k3_xboole_0(sK2,X0)))
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f2254,f493])).

fof(f493,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_10 ),
    inference(superposition,[],[f480,f274])).

fof(f480,plain,
    ( ! [X2] : m1_subset_1(k3_xboole_0(X2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_10 ),
    inference(forward_demodulation,[],[f479,f472])).

fof(f472,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),sK2,X1) = k3_xboole_0(X1,sK2)
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f462,f377])).

fof(f377,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_10 ),
    inference(avatar_component_clause,[],[f376])).

fof(f462,plain,
    ( ! [X1] :
        ( k9_subset_1(u1_struct_0(sK0),sK2,X1) = k3_xboole_0(X1,sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_10 ),
    inference(superposition,[],[f387,f291])).

fof(f387,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)
    | ~ spl29_10 ),
    inference(resolution,[],[f377,f292])).

fof(f479,plain,
    ( ! [X2] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,X2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f466,f377])).

fof(f466,plain,
    ( ! [X2] :
        ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_10 ),
    inference(superposition,[],[f290,f387])).

fof(f2254,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(sK2,X0) = k3_xboole_0(sK2,sK8(sK0,sK2,k3_xboole_0(sK2,X0))) )
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(resolution,[],[f911,f273])).

fof(f273,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',t17_xboole_1)).

fof(f911,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(sK2,sK8(sK0,sK2,X1)) = X1 )
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(forward_demodulation,[],[f910,f274])).

fof(f910,plain,
    ( ! [X1] :
        ( k3_xboole_0(sK8(sK0,sK2,X1),sK2) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK2) )
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(forward_demodulation,[],[f909,f472])).

fof(f909,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK2)
        | k9_subset_1(u1_struct_0(sK0),sK2,sK8(sK0,sK2,X1)) = X1 )
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f903,f377])).

fof(f903,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK2)
        | k9_subset_1(u1_struct_0(sK0),sK2,sK8(sK0,sK2,X1)) = X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_8 ),
    inference(resolution,[],[f340,f370])).

fof(f370,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl29_8 ),
    inference(avatar_component_clause,[],[f369])).

fof(f340,plain,
    ( ! [X6,X7] :
        ( ~ v2_tex_2(X6,sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X7,X6)
        | k9_subset_1(u1_struct_0(sK0),X6,sK8(sK0,X6,X7)) = X7
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0 ),
    inference(resolution,[],[f334,f227])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK8(X0,X1,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f120])).

fof(f120,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',d5_tex_2)).

fof(f334,plain,
    ( l1_pre_topc(sK0)
    | ~ spl29_0 ),
    inference(avatar_component_clause,[],[f333])).

fof(f7038,plain,
    ( ! [X0] : v3_pre_topc(k3_xboole_0(sK2,X0),sK0)
    | ~ spl29_0
    | ~ spl29_4
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f7037,f370])).

fof(f7037,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(sK2,X0),sK0)
        | ~ v2_tex_2(sK2,sK0) )
    | ~ spl29_0
    | ~ spl29_4
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f7036,f377])).

fof(f7036,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(sK2,X0),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK2,sK0) )
    | ~ spl29_0
    | ~ spl29_4
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f7035,f273])).

fof(f7035,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(sK2,X0),sK0)
        | ~ r1_tarski(k3_xboole_0(sK2,X0),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK2,sK0) )
    | ~ spl29_0
    | ~ spl29_4
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f7026,f493])).

fof(f7026,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(sK2,X0),sK0)
        | ~ m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_xboole_0(sK2,X0),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK2,sK0) )
    | ~ spl29_0
    | ~ spl29_4
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(resolution,[],[f2920,f339])).

fof(f339,plain,
    ( ! [X4,X5] :
        ( v3_pre_topc(sK8(sK0,X4,X5),sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X5,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X4,sK0) )
    | ~ spl29_0 ),
    inference(resolution,[],[f334,f226])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v3_pre_topc(sK8(X0,X1,X2),X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f2920,plain,
    ( ! [X10] :
        ( ~ v3_pre_topc(sK8(sK0,sK2,k3_xboole_0(sK2,X10)),sK0)
        | v3_pre_topc(k3_xboole_0(sK2,X10),sK0) )
    | ~ spl29_0
    | ~ spl29_4
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f2919,f377])).

fof(f2919,plain,
    ( ! [X10] :
        ( v3_pre_topc(k3_xboole_0(sK2,X10),sK0)
        | ~ v3_pre_topc(sK8(sK0,sK2,k3_xboole_0(sK2,X10)),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_4
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f2918,f356])).

fof(f356,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl29_4 ),
    inference(avatar_component_clause,[],[f355])).

fof(f2918,plain,
    ( ! [X10] :
        ( v3_pre_topc(k3_xboole_0(sK2,X10),sK0)
        | ~ v3_pre_topc(sK2,sK0)
        | ~ v3_pre_topc(sK8(sK0,sK2,k3_xboole_0(sK2,X10)),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f2914,f2242])).

fof(f2242,plain,
    ( ! [X0] : m1_subset_1(sK8(sK0,sK2,k3_xboole_0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f2239,f493])).

fof(f2239,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK8(sK0,sK2,k3_xboole_0(sK2,X0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(resolution,[],[f895,f273])).

fof(f895,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK8(sK0,sK2,X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f891,f377])).

fof(f891,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X1,sK2)
        | m1_subset_1(sK8(sK0,sK2,X1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_8 ),
    inference(resolution,[],[f338,f370])).

fof(f338,plain,
    ( ! [X2,X3] :
        ( ~ v2_tex_2(X2,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,X2)
        | m1_subset_1(sK8(sK0,X2,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0 ),
    inference(resolution,[],[f334,f225])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(sK8(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f2914,plain,
    ( ! [X10] :
        ( v3_pre_topc(k3_xboole_0(sK2,X10),sK0)
        | ~ m1_subset_1(sK8(sK0,sK2,k3_xboole_0(sK2,X10)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK2,sK0)
        | ~ v3_pre_topc(sK8(sK0,sK2,k3_xboole_0(sK2,X10)),sK0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_8
    | ~ spl29_10 ),
    inference(superposition,[],[f417,f2257])).

fof(f417,plain,(
    ! [X2,X3] :
      ( v3_pre_topc(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f416])).

fof(f416,plain,(
    ! [X2,X3] :
      ( v3_pre_topc(k3_xboole_0(X2,X3),sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X2,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f191,f291])).

fof(f191,plain,(
    ! [X2,X1] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v3_pre_topc(X2,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ? [X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              & v2_tex_2(X4,X0)
              & v2_tex_2(X3,X0)
              & v3_pre_topc(X4,X0)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      & ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              | ~ v3_pre_topc(X2,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f103])).

fof(f103,plain,(
    ? [X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ v2_tex_2(k4_subset_1(u1_struct_0(X0),X3,X4),X0)
              & v2_tex_2(X4,X0)
              & v2_tex_2(X3,X0)
              & v3_pre_topc(X4,X0)
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
      & ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              | ~ v3_pre_topc(X2,X0)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f100])).

fof(f100,plain,(
    ~ ! [X0] :
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
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',t30_tex_2)).

fof(f22510,plain,
    ( v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ v3_pre_topc(k3_xboole_0(sK7(sK0,k2_xboole_0(sK1,sK2)),sK2),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK7(sK0,k2_xboole_0(sK1,sK2)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_6
    | ~ spl29_12
    | ~ spl29_120
    | ~ spl29_214 ),
    inference(subsumption_resolution,[],[f22509,f7006])).

fof(f7006,plain,
    ( ! [X0] : v3_pre_topc(k3_xboole_0(sK1,X0),sK0)
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f7005,f363])).

fof(f363,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl29_6 ),
    inference(avatar_component_clause,[],[f362])).

fof(f7005,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(sK1,X0),sK0)
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f7004,f384])).

fof(f384,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_12 ),
    inference(avatar_component_clause,[],[f383])).

fof(f7004,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(sK1,X0),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f7003,f273])).

fof(f7003,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(sK1,X0),sK0)
        | ~ r1_tarski(k3_xboole_0(sK1,X0),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f6994,f521])).

fof(f521,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_12 ),
    inference(superposition,[],[f513,f274])).

fof(f513,plain,
    ( ! [X2] : m1_subset_1(k3_xboole_0(X2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_12 ),
    inference(forward_demodulation,[],[f512,f505])).

fof(f505,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),sK1,X1) = k3_xboole_0(X1,sK1)
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f495,f384])).

fof(f495,plain,
    ( ! [X1] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,X1) = k3_xboole_0(X1,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_12 ),
    inference(superposition,[],[f391,f291])).

fof(f391,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X1)
    | ~ spl29_12 ),
    inference(resolution,[],[f384,f292])).

fof(f512,plain,
    ( ! [X2] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f499,f384])).

fof(f499,plain,
    ( ! [X2] :
        ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_12 ),
    inference(superposition,[],[f290,f391])).

fof(f6994,plain,
    ( ! [X0] :
        ( v3_pre_topc(k3_xboole_0(sK1,X0),sK0)
        | ~ m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k3_xboole_0(sK1,X0),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(sK1,sK0) )
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(resolution,[],[f2899,f339])).

fof(f2899,plain,
    ( ! [X9] :
        ( ~ v3_pre_topc(sK8(sK0,sK1,k3_xboole_0(sK1,X9)),sK0)
        | v3_pre_topc(k3_xboole_0(sK1,X9),sK0) )
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f2898,f384])).

fof(f2898,plain,
    ( ! [X9] :
        ( v3_pre_topc(k3_xboole_0(sK1,X9),sK0)
        | ~ v3_pre_topc(sK8(sK0,sK1,k3_xboole_0(sK1,X9)),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_2
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f2897,f349])).

fof(f349,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl29_2 ),
    inference(avatar_component_clause,[],[f348])).

fof(f2897,plain,
    ( ! [X9] :
        ( v3_pre_topc(k3_xboole_0(sK1,X9),sK0)
        | ~ v3_pre_topc(sK1,sK0)
        | ~ v3_pre_topc(sK8(sK0,sK1,k3_xboole_0(sK1,X9)),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f2893,f2237])).

fof(f2237,plain,
    ( ! [X0] : m1_subset_1(sK8(sK0,sK1,k3_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_0
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f2234,f521])).

fof(f2234,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK8(sK0,sK1,k3_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(resolution,[],[f894,f273])).

fof(f894,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK8(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f890,f384])).

fof(f890,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | m1_subset_1(sK8(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_6 ),
    inference(resolution,[],[f338,f363])).

fof(f2893,plain,
    ( ! [X9] :
        ( v3_pre_topc(k3_xboole_0(sK1,X9),sK0)
        | ~ m1_subset_1(sK8(sK0,sK1,k3_xboole_0(sK1,X9)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ v3_pre_topc(sK8(sK0,sK1,k3_xboole_0(sK1,X9)),sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(superposition,[],[f417,f2253])).

fof(f2253,plain,
    ( ! [X0] : k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,sK8(sK0,sK1,k3_xboole_0(sK1,X0)))
    | ~ spl29_0
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f2250,f521])).

fof(f2250,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(sK1,X0) = k3_xboole_0(sK1,sK8(sK0,sK1,k3_xboole_0(sK1,X0))) )
    | ~ spl29_0
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(resolution,[],[f908,f273])).

fof(f908,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(sK1,sK8(sK0,sK1,X0)) = X0 )
    | ~ spl29_0
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(forward_demodulation,[],[f907,f274])).

fof(f907,plain,
    ( ! [X0] :
        ( k3_xboole_0(sK8(sK0,sK1,X0),sK1) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl29_0
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(forward_demodulation,[],[f906,f505])).

fof(f906,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,sK8(sK0,sK1,X0)) = X0 )
    | ~ spl29_0
    | ~ spl29_6
    | ~ spl29_12 ),
    inference(subsumption_resolution,[],[f902,f384])).

fof(f902,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1)
        | k9_subset_1(u1_struct_0(sK0),sK1,sK8(sK0,sK1,X0)) = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0
    | ~ spl29_6 ),
    inference(resolution,[],[f340,f363])).

fof(f22509,plain,
    ( v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ v3_pre_topc(k3_xboole_0(sK1,sK7(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ v3_pre_topc(k3_xboole_0(sK7(sK0,k2_xboole_0(sK1,sK2)),sK2),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK7(sK0,k2_xboole_0(sK1,sK2)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_120
    | ~ spl29_214 ),
    inference(subsumption_resolution,[],[f22476,f6450])).

fof(f22476,plain,
    ( v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK7(sK0,k2_xboole_0(sK1,sK2)),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(k3_xboole_0(sK1,sK7(sK0,k2_xboole_0(sK1,sK2))),sK0)
    | ~ v3_pre_topc(k3_xboole_0(sK7(sK0,k2_xboole_0(sK1,sK2)),sK2),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK7(sK0,k2_xboole_0(sK1,sK2)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_214 ),
    inference(superposition,[],[f5891,f3471])).

fof(f5891,plain,(
    ! [X4,X2,X3] :
      ( v3_pre_topc(k3_xboole_0(k2_xboole_0(X3,X4),X2),sK0)
      | ~ m1_subset_1(k3_xboole_0(X2,X4),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k3_xboole_0(X3,X2),sK0)
      | ~ v3_pre_topc(k3_xboole_0(X2,X4),sK0)
      | ~ m1_subset_1(k3_xboole_0(X2,X3),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f2545,f274])).

fof(f2545,plain,(
    ! [X6,X4,X5] :
      ( v3_pre_topc(k3_xboole_0(X4,k2_xboole_0(X5,X6)),sK0)
      | ~ m1_subset_1(k3_xboole_0(X4,X6),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(k3_xboole_0(X5,X4),sK0)
      | ~ v3_pre_topc(k3_xboole_0(X4,X6),sK0)
      | ~ m1_subset_1(k3_xboole_0(X4,X5),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f882,f274])).

fof(f882,plain,(
    ! [X6,X8,X7] :
      ( ~ v3_pre_topc(k3_xboole_0(X6,X7),sK0)
      | ~ m1_subset_1(k3_xboole_0(X6,X8),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(k3_xboole_0(X6,k2_xboole_0(X7,X8)),sK0)
      | ~ v3_pre_topc(k3_xboole_0(X6,X8),sK0)
      | ~ m1_subset_1(k3_xboole_0(X6,X7),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f428,f288])).

fof(f288,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',t23_xboole_1)).

fof(f428,plain,(
    ! [X2,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v3_pre_topc(X2,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f427])).

fof(f427,plain,(
    ! [X2,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v3_pre_topc(X2,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f192,f296])).

fof(f296,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f187])).

fof(f187,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f186])).

fof(f186,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f85])).

fof(f85,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',redefinition_k4_subset_1)).

fof(f192,plain,(
    ! [X2,X1] :
      ( v3_pre_topc(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ v3_pre_topc(X2,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f19046,plain,
    ( ~ spl29_745
    | spl29_746
    | ~ spl29_0
    | ~ spl29_120 ),
    inference(avatar_split_clause,[],[f4365,f2222,f333,f19044,f19041])).

fof(f19041,plain,
    ( spl29_745
  <=> ~ v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_745])])).

fof(f4365,plain,
    ( ! [X2] :
        ( k3_xboole_0(X2,sK7(sK0,k2_xboole_0(sK1,sK2))) != sK7(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0)
        | v2_tex_2(X2,sK0) )
    | ~ spl29_0
    | ~ spl29_120 ),
    inference(forward_demodulation,[],[f4364,f4358])).

fof(f4364,plain,
    ( ! [X2] :
        ( k9_subset_1(u1_struct_0(sK0),sK7(sK0,k2_xboole_0(sK1,sK2)),X2) != sK7(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0)
        | v2_tex_2(X2,sK0) )
    | ~ spl29_0
    | ~ spl29_120 ),
    inference(subsumption_resolution,[],[f4363,f334])).

fof(f4363,plain,
    ( ! [X2] :
        ( k9_subset_1(u1_struct_0(sK0),sK7(sK0,k2_xboole_0(sK1,sK2)),X2) != sK7(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(X2,sK0) )
    | ~ spl29_120 ),
    inference(subsumption_resolution,[],[f4343,f2223])).

fof(f4343,plain,
    ( ! [X2] :
        ( k9_subset_1(u1_struct_0(sK0),sK7(sK0,k2_xboole_0(sK1,sK2)),X2) != sK7(sK0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK7(sK0,k2_xboole_0(sK1,sK2)),sK0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(X2,sK0) )
    | ~ spl29_120 ),
    inference(superposition,[],[f224,f2613])).

fof(f224,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK7(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f3472,plain,
    ( spl29_214
    | ~ spl29_0
    | spl29_19
    | ~ spl29_118 ),
    inference(avatar_split_clause,[],[f2779,f2213,f423,f333,f3470])).

fof(f2779,plain,
    ( k3_xboole_0(k2_xboole_0(sK1,sK2),sK7(sK0,k2_xboole_0(sK1,sK2))) = sK7(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl29_0
    | ~ spl29_19
    | ~ spl29_118 ),
    inference(subsumption_resolution,[],[f2265,f2214])).

fof(f2265,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_xboole_0(k2_xboole_0(sK1,sK2),sK7(sK0,k2_xboole_0(sK1,sK2))) = sK7(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl29_0
    | ~ spl29_19 ),
    inference(resolution,[],[f537,f424])).

fof(f537,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(X0,sK7(sK0,X0)) = sK7(sK0,X0) )
    | ~ spl29_0 ),
    inference(forward_demodulation,[],[f536,f274])).

fof(f536,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0)
        | k3_xboole_0(sK7(sK0,X0),X0) = sK7(sK0,X0) )
    | ~ spl29_0 ),
    inference(resolution,[],[f342,f279])).

fof(f279,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f91])).

fof(f91,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',t28_xboole_1)).

fof(f342,plain,
    ( ! [X9] :
        ( r1_tarski(sK7(sK0,X9),X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X9,sK0) )
    | ~ spl29_0 ),
    inference(resolution,[],[f334,f229])).

fof(f229,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK7(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f2775,plain,
    ( ~ spl29_10
    | ~ spl29_12
    | spl29_119 ),
    inference(avatar_contradiction_clause,[],[f2774])).

fof(f2774,plain,
    ( $false
    | ~ spl29_10
    | ~ spl29_12
    | ~ spl29_119 ),
    inference(subsumption_resolution,[],[f2764,f384])).

fof(f2764,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_10
    | ~ spl29_119 ),
    inference(resolution,[],[f1169,f2217])).

fof(f2217,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_119 ),
    inference(avatar_component_clause,[],[f2216])).

fof(f2216,plain,
    ( spl29_119
  <=> ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_119])])).

fof(f1169,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_xboole_0(X3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f1161,f377])).

fof(f1161,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_xboole_0(X3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_10 ),
    inference(duplicate_literal_removal,[],[f1160])).

fof(f1160,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_xboole_0(X3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_10 ),
    inference(superposition,[],[f295,f563])).

fof(f563,plain,
    ( ! [X1] :
        ( k4_subset_1(u1_struct_0(sK0),sK2,X1) = k2_xboole_0(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_10 ),
    inference(subsumption_resolution,[],[f562,f377])).

fof(f562,plain,
    ( ! [X1] :
        ( k4_subset_1(u1_struct_0(sK0),sK2,X1) = k2_xboole_0(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_10 ),
    inference(duplicate_literal_removal,[],[f547])).

fof(f547,plain,
    ( ! [X1] :
        ( k4_subset_1(u1_struct_0(sK0),sK2,X1) = k2_xboole_0(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_10 ),
    inference(superposition,[],[f386,f296])).

fof(f386,plain,
    ( ! [X0] :
        ( k4_subset_1(u1_struct_0(sK0),X0,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_10 ),
    inference(resolution,[],[f377,f297])).

fof(f297,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f189])).

fof(f189,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f188])).

fof(f188,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',commutativity_k4_subset_1)).

fof(f295,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f185])).

fof(f185,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f184])).

fof(f184,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t30_tex_2.p',dt_k4_subset_1)).

fof(f2224,plain,
    ( ~ spl29_119
    | spl29_120
    | ~ spl29_0
    | spl29_19 ),
    inference(avatar_split_clause,[],[f539,f423,f333,f2222,f2216])).

fof(f539,plain,
    ( m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_0
    | ~ spl29_19 ),
    inference(resolution,[],[f341,f424])).

fof(f341,plain,
    ( ! [X8] :
        ( v2_tex_2(X8,sK0)
        | m1_subset_1(sK7(sK0,X8),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl29_0 ),
    inference(resolution,[],[f334,f228])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK7(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f425,plain,
    ( ~ spl29_19
    | ~ spl29_10
    | ~ spl29_12
    | spl29_17 ),
    inference(avatar_split_clause,[],[f414,f405,f383,f376,f423])).

fof(f405,plain,
    ( spl29_17
  <=> ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl29_17])])).

fof(f414,plain,
    ( ~ v2_tex_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl29_10
    | ~ spl29_12
    | ~ spl29_17 ),
    inference(subsumption_resolution,[],[f413,f384])).

fof(f413,plain,
    ( ~ v2_tex_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_10
    | ~ spl29_17 ),
    inference(subsumption_resolution,[],[f412,f377])).

fof(f412,plain,
    ( ~ v2_tex_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl29_17 ),
    inference(superposition,[],[f406,f296])).

fof(f406,plain,
    ( ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl29_17 ),
    inference(avatar_component_clause,[],[f405])).

fof(f407,plain,(
    ~ spl29_17 ),
    inference(avatar_split_clause,[],[f198,f405])).

fof(f198,plain,(
    ~ v2_tex_2(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f385,plain,(
    spl29_12 ),
    inference(avatar_split_clause,[],[f199,f383])).

fof(f199,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f104])).

fof(f378,plain,(
    spl29_10 ),
    inference(avatar_split_clause,[],[f193,f376])).

fof(f193,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f104])).

fof(f371,plain,(
    spl29_8 ),
    inference(avatar_split_clause,[],[f197,f369])).

fof(f197,plain,(
    v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f364,plain,(
    spl29_6 ),
    inference(avatar_split_clause,[],[f196,f362])).

fof(f196,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f357,plain,(
    spl29_4 ),
    inference(avatar_split_clause,[],[f195,f355])).

fof(f195,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f350,plain,(
    spl29_2 ),
    inference(avatar_split_clause,[],[f194,f348])).

fof(f194,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f335,plain,(
    spl29_0 ),
    inference(avatar_split_clause,[],[f200,f333])).

fof(f200,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f104])).
%------------------------------------------------------------------------------
