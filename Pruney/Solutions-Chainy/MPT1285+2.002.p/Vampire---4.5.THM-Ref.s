%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:05 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  241 (1155 expanded)
%              Number of leaves         :   42 ( 477 expanded)
%              Depth                    :   21
%              Number of atoms          :  785 (10223 expanded)
%              Number of equality atoms :   69 ( 203 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f120,f121,f153,f254,f358,f555,f566,f634,f656,f753,f874,f1482,f1792,f1856,f1925,f1931,f2427,f3277,f3329])).

fof(f3329,plain,
    ( spl4_1
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f3328])).

fof(f3328,plain,
    ( $false
    | spl4_1
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3327,f56])).

fof(f56,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v3_pre_topc(sK2,sK0) )
        & v6_tops_1(sK2,sK0) )
      | ( ~ v6_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f45,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | ( ~ v6_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v3_pre_topc(X2,sK0) )
                      & v6_tops_1(X2,sK0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK0)
                      | ~ v3_pre_topc(X2,sK0) )
                    & v6_tops_1(X2,sK0) )
                  | ( ~ v6_tops_1(X3,X1)
                    & v4_tops_1(X3,X1)
                    & v3_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK0)
                    | ~ v3_pre_topc(X2,sK0) )
                  & v6_tops_1(X2,sK0) )
                | ( ~ v6_tops_1(X3,sK1)
                  & v4_tops_1(X3,sK1)
                  & v3_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK0)
                  | ~ v3_pre_topc(X2,sK0) )
                & v6_tops_1(X2,sK0) )
              | ( ~ v6_tops_1(X3,sK1)
                & v4_tops_1(X3,sK1)
                & v3_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK2,sK0)
                | ~ v3_pre_topc(sK2,sK0) )
              & v6_tops_1(sK2,sK0) )
            | ( ~ v6_tops_1(X3,sK1)
              & v4_tops_1(X3,sK1)
              & v3_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK2,sK0)
              | ~ v3_pre_topc(sK2,sK0) )
            & v6_tops_1(sK2,sK0) )
          | ( ~ v6_tops_1(X3,sK1)
            & v4_tops_1(X3,sK1)
            & v3_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ( ~ v4_tops_1(sK2,sK0)
            | ~ v3_pre_topc(sK2,sK0) )
          & v6_tops_1(sK2,sK0) )
        | ( ~ v6_tops_1(sK3,sK1)
          & v4_tops_1(sK3,sK1)
          & v3_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

fof(f3327,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_1
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3326,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f3326,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | spl4_1
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f3314,f95])).

fof(f95,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_1
  <=> v6_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f3314,plain,
    ( v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_23 ),
    inference(trivial_inequality_removal,[],[f3312])).

fof(f3312,plain,
    ( sK3 != sK3
    | v6_tops_1(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_23 ),
    inference(superposition,[],[f73,f253])).

fof(f253,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl4_23
  <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f3277,plain,
    ( spl4_22
    | ~ spl4_48
    | ~ spl4_69
    | ~ spl4_149 ),
    inference(avatar_contradiction_clause,[],[f3276])).

fof(f3276,plain,
    ( $false
    | spl4_22
    | ~ spl4_48
    | ~ spl4_69
    | ~ spl4_149 ),
    inference(subsumption_resolution,[],[f3275,f249])).

fof(f249,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl4_22
  <=> r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f3275,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl4_48
    | ~ spl4_69
    | ~ spl4_149 ),
    inference(forward_demodulation,[],[f3274,f2195])).

fof(f2195,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ spl4_48
    | ~ spl4_149 ),
    inference(forward_demodulation,[],[f2177,f354])).

fof(f354,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3)) ),
    inference(backward_demodulation,[],[f191,f192])).

fof(f192,plain,(
    k3_subset_1(u1_struct_0(sK1),sK3) = k4_xboole_0(u1_struct_0(sK1),sK3) ),
    inference(resolution,[],[f58,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f191,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f58,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2177,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3))
    | ~ spl4_48
    | ~ spl4_149 ),
    inference(backward_demodulation,[],[f1249,f1337])).

fof(f1337,plain,
    ( k4_xboole_0(u1_struct_0(sK1),sK3) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3))
    | ~ spl4_149 ),
    inference(avatar_component_clause,[],[f1335])).

fof(f1335,plain,
    ( spl4_149
  <=> k4_xboole_0(u1_struct_0(sK1),sK3) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_149])])).

fof(f1249,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)))
    | ~ spl4_48 ),
    inference(backward_demodulation,[],[f457,f728])).

fof(f728,plain,
    ( k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3))
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f685,f457])).

fof(f685,plain,
    ( k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))))
    | ~ spl4_48 ),
    inference(resolution,[],[f476,f80])).

fof(f476,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f475])).

fof(f475,plain,
    ( spl4_48
  <=> m1_subset_1(k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f457,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))) ),
    inference(forward_demodulation,[],[f194,f192])).

fof(f194,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) ),
    inference(subsumption_resolution,[],[f181,f56])).

fof(f181,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f58,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f3274,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl4_48
    | ~ spl4_69
    | ~ spl4_149 ),
    inference(subsumption_resolution,[],[f3237,f193])).

fof(f193,plain,(
    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f180,f56])).

fof(f180,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f58,f65])).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f3237,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ spl4_48
    | ~ spl4_69
    | ~ spl4_149 ),
    inference(resolution,[],[f2562,f58])).

fof(f2562,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
        | ~ r1_tarski(X0,k2_pre_topc(sK1,sK3)) )
    | ~ spl4_48
    | ~ spl4_69
    | ~ spl4_149 ),
    inference(subsumption_resolution,[],[f2552,f56])).

fof(f2552,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_pre_topc(sK1,sK3))
        | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ l1_pre_topc(sK1) )
    | ~ spl4_48
    | ~ spl4_69
    | ~ spl4_149 ),
    inference(resolution,[],[f2247,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
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
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f2247,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_48
    | ~ spl4_69
    | ~ spl4_149 ),
    inference(backward_demodulation,[],[f633,f2195])).

fof(f633,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f631])).

fof(f631,plain,
    ( spl4_69
  <=> m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f2427,plain,
    ( spl4_3
    | ~ spl4_9
    | ~ spl4_57
    | ~ spl4_194 ),
    inference(avatar_contradiction_clause,[],[f2426])).

fof(f2426,plain,
    ( $false
    | spl4_3
    | ~ spl4_9
    | ~ spl4_57
    | ~ spl4_194 ),
    inference(subsumption_resolution,[],[f2425,f103])).

fof(f103,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_3
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2425,plain,
    ( v4_tops_1(sK2,sK0)
    | ~ spl4_9
    | ~ spl4_57
    | ~ spl4_194 ),
    inference(forward_demodulation,[],[f2367,f152])).

fof(f152,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl4_9
  <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f2367,plain,
    ( v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ spl4_9
    | ~ spl4_57
    | ~ spl4_194 ),
    inference(backward_demodulation,[],[f561,f1858])).

fof(f1858,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl4_9
    | ~ spl4_194 ),
    inference(forward_demodulation,[],[f1857,f152])).

fof(f1857,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))
    | ~ spl4_194 ),
    inference(subsumption_resolution,[],[f1805,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f1805,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_194 ),
    inference(resolution,[],[f1781,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f1781,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_194 ),
    inference(avatar_component_clause,[],[f1780])).

fof(f1780,plain,
    ( spl4_194
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f561,plain,
    ( v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),sK0)
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f559])).

fof(f559,plain,
    ( spl4_57
  <=> v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f1931,plain,
    ( ~ spl4_35
    | spl4_149
    | ~ spl4_33
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f1930,f475,f343,f1335,f366])).

fof(f366,plain,
    ( spl4_35
  <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f343,plain,
    ( spl4_33
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f1930,plain,
    ( k4_xboole_0(u1_struct_0(sK1),sK3) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3))
    | ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | ~ spl4_33
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f1929,f728])).

fof(f1929,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f390,f56])).

fof(f390,plain,
    ( ~ v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_33 ),
    inference(resolution,[],[f378,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f378,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f344,f192])).

fof(f344,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f343])).

fof(f1925,plain,
    ( spl4_35
    | ~ spl4_5
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f1924,f343,f111,f366])).

fof(f111,plain,
    ( spl4_5
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1924,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f1923,f56])).

fof(f1923,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f435,f378])).

fof(f435,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f71,f354])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f1856,plain,
    ( spl4_2
    | ~ spl4_9
    | ~ spl4_194 ),
    inference(avatar_contradiction_clause,[],[f1855])).

fof(f1855,plain,
    ( $false
    | spl4_2
    | ~ spl4_9
    | ~ spl4_194 ),
    inference(subsumption_resolution,[],[f1854,f99])).

fof(f99,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1854,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_9
    | ~ spl4_194 ),
    inference(forward_demodulation,[],[f1853,f152])).

fof(f1853,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ spl4_194 ),
    inference(subsumption_resolution,[],[f1852,f54])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f1852,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_194 ),
    inference(subsumption_resolution,[],[f1804,f55])).

fof(f1804,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_194 ),
    inference(resolution,[],[f1781,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f1792,plain,(
    spl4_194 ),
    inference(avatar_contradiction_clause,[],[f1791])).

fof(f1791,plain,
    ( $false
    | spl4_194 ),
    inference(subsumption_resolution,[],[f1790,f55])).

fof(f1790,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_194 ),
    inference(subsumption_resolution,[],[f1788,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f1788,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_194 ),
    inference(resolution,[],[f1782,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f1782,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_194 ),
    inference(avatar_component_clause,[],[f1780])).

fof(f1482,plain,
    ( ~ spl4_55
    | ~ spl4_56
    | spl4_58 ),
    inference(avatar_contradiction_clause,[],[f1481])).

fof(f1481,plain,
    ( $false
    | ~ spl4_55
    | ~ spl4_56
    | spl4_58 ),
    inference(subsumption_resolution,[],[f1480,f841])).

fof(f841,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f840,f137])).

fof(f137,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))) ),
    inference(subsumption_resolution,[],[f124,f55])).

fof(f124,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_1)).

fof(f840,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))))
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f818,f55])).

fof(f818,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_55 ),
    inference(resolution,[],[f549,f65])).

fof(f549,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl4_55
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f1480,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ spl4_56
    | spl4_58 ),
    inference(forward_demodulation,[],[f1476,f137])).

fof(f1476,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))))
    | ~ spl4_56
    | spl4_58 ),
    inference(backward_demodulation,[],[f565,f816])).

fof(f816,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f764,f55])).

fof(f764,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_56 ),
    inference(resolution,[],[f554,f84])).

fof(f554,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl4_56
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f565,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))))
    | spl4_58 ),
    inference(avatar_component_clause,[],[f563])).

fof(f563,plain,
    ( spl4_58
  <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f874,plain,(
    spl4_68 ),
    inference(avatar_contradiction_clause,[],[f873])).

fof(f873,plain,
    ( $false
    | spl4_68 ),
    inference(subsumption_resolution,[],[f872,f56])).

fof(f872,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_68 ),
    inference(subsumption_resolution,[],[f870,f58])).

fof(f870,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | spl4_68 ),
    inference(resolution,[],[f869,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f869,plain,
    ( ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_68 ),
    inference(subsumption_resolution,[],[f867,f56])).

fof(f867,plain,
    ( ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | spl4_68 ),
    inference(resolution,[],[f745,f82])).

fof(f745,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_68 ),
    inference(subsumption_resolution,[],[f743,f56])).

fof(f743,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | spl4_68 ),
    inference(resolution,[],[f629,f83])).

fof(f629,plain,
    ( ~ m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_68 ),
    inference(avatar_component_clause,[],[f627])).

fof(f627,plain,
    ( spl4_68
  <=> m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f753,plain,(
    spl4_55 ),
    inference(avatar_contradiction_clause,[],[f752])).

fof(f752,plain,
    ( $false
    | spl4_55 ),
    inference(subsumption_resolution,[],[f751,f55])).

fof(f751,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_55 ),
    inference(subsumption_resolution,[],[f749,f57])).

fof(f749,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_55 ),
    inference(resolution,[],[f748,f83])).

fof(f748,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_55 ),
    inference(subsumption_resolution,[],[f746,f55])).

fof(f746,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_55 ),
    inference(resolution,[],[f732,f82])).

fof(f732,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_55 ),
    inference(subsumption_resolution,[],[f730,f55])).

fof(f730,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_55 ),
    inference(resolution,[],[f550,f83])).

fof(f550,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_55 ),
    inference(avatar_component_clause,[],[f548])).

fof(f656,plain,
    ( ~ spl4_33
    | spl4_48 ),
    inference(avatar_contradiction_clause,[],[f655])).

fof(f655,plain,
    ( $false
    | ~ spl4_33
    | spl4_48 ),
    inference(subsumption_resolution,[],[f654,f56])).

fof(f654,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl4_33
    | spl4_48 ),
    inference(subsumption_resolution,[],[f652,f378])).

fof(f652,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | spl4_48 ),
    inference(resolution,[],[f477,f82])).

fof(f477,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_48 ),
    inference(avatar_component_clause,[],[f475])).

fof(f634,plain,
    ( ~ spl4_68
    | spl4_69 ),
    inference(avatar_split_clause,[],[f625,f631,f627])).

fof(f625,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f620,f56])).

fof(f620,plain,
    ( m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f82,f195])).

fof(f195,plain,(
    k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))) ),
    inference(subsumption_resolution,[],[f182,f56])).

fof(f182,plain,
    ( k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f58,f67])).

fof(f566,plain,
    ( ~ spl4_55
    | spl4_57
    | ~ spl4_58 ),
    inference(avatar_split_clause,[],[f557,f563,f559,f548])).

fof(f557,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))))
    | v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f556,f55])).

fof(f556,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))))
    | v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f542,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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

fof(f542,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))))
    | v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f76,f137])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(f555,plain,
    ( ~ spl4_55
    | spl4_56 ),
    inference(avatar_split_clause,[],[f546,f552,f548])).

fof(f546,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f541,f55])).

fof(f541,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f82,f137])).

fof(f358,plain,(
    spl4_33 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl4_33 ),
    inference(subsumption_resolution,[],[f352,f78])).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f352,plain,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1))
    | spl4_33 ),
    inference(backward_demodulation,[],[f351,f192])).

fof(f351,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK1),sK3),u1_struct_0(sK1))
    | spl4_33 ),
    inference(resolution,[],[f345,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f345,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl4_33 ),
    inference(avatar_component_clause,[],[f343])).

fof(f254,plain,
    ( ~ spl4_22
    | spl4_23
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f245,f106,f251,f247])).

fof(f106,plain,
    ( spl4_4
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f245,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl4_4 ),
    inference(resolution,[],[f207,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f207,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f206,f56])).

fof(f206,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f185,f108])).

fof(f108,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f185,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f58,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tops_1(X1,X0)
      | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f153,plain,
    ( spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f148,f116,f150])).

fof(f116,plain,
    ( spl4_6
  <=> v6_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f148,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f126,f55])).

fof(f126,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f57,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f121,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f59,f116,f111])).

fof(f59,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f120,plain,
    ( spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f60,f116,f106])).

fof(f60,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f119,plain,
    ( ~ spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f61,f116,f93])).

fof(f61,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f114,plain,
    ( spl4_5
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f62,f101,f97,f111])).

fof(f62,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f109,plain,
    ( spl4_4
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f63,f101,f97,f106])).

fof(f63,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f104,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f64,f101,f97,f93])).

fof(f64,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:23:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (9228)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (9231)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (9230)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (9226)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (9225)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (9223)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (9222)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.55  % (9241)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.55  % (9232)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (9233)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.56  % (9240)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.57  % (9238)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.60/0.57  % (9227)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.60/0.57  % (9242)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.60/0.57  % (9224)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.60/0.58  % (9234)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.60/0.59  % (9236)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.82/0.60  % (9245)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.82/0.60  % (9237)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.82/0.61  % (9243)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.82/0.61  % (9235)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.82/0.61  % (9244)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.82/0.61  % (9246)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.82/0.62  % (9229)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.82/0.62  % (9247)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.82/0.64  % (9239)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 2.21/0.66  % (9231)Refutation not found, incomplete strategy% (9231)------------------------------
% 2.21/0.66  % (9231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.66  % (9231)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.66  
% 2.21/0.66  % (9231)Memory used [KB]: 6140
% 2.21/0.66  % (9231)Time elapsed: 0.215 s
% 2.21/0.66  % (9231)------------------------------
% 2.21/0.66  % (9231)------------------------------
% 2.21/0.69  % (9223)Refutation found. Thanks to Tanya!
% 2.21/0.69  % SZS status Theorem for theBenchmark
% 2.21/0.69  % SZS output start Proof for theBenchmark
% 2.21/0.69  fof(f3330,plain,(
% 2.21/0.69    $false),
% 2.21/0.69    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f120,f121,f153,f254,f358,f555,f566,f634,f656,f753,f874,f1482,f1792,f1856,f1925,f1931,f2427,f3277,f3329])).
% 2.21/0.69  fof(f3329,plain,(
% 2.21/0.69    spl4_1 | ~spl4_23),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f3328])).
% 2.21/0.69  fof(f3328,plain,(
% 2.21/0.69    $false | (spl4_1 | ~spl4_23)),
% 2.21/0.69    inference(subsumption_resolution,[],[f3327,f56])).
% 2.21/0.69  fof(f56,plain,(
% 2.21/0.69    l1_pre_topc(sK1)),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f46,plain,(
% 2.21/0.69    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.21/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f45,f44,f43,f42])).
% 2.21/0.69  fof(f42,plain,(
% 2.21/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.21/0.69    introduced(choice_axiom,[])).
% 2.21/0.69  fof(f43,plain,(
% 2.21/0.69    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 2.21/0.69    introduced(choice_axiom,[])).
% 2.21/0.69  fof(f44,plain,(
% 2.21/0.69    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.21/0.69    introduced(choice_axiom,[])).
% 2.21/0.69  fof(f45,plain,(
% 2.21/0.69    ? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 2.21/0.69    introduced(choice_axiom,[])).
% 2.21/0.69  fof(f21,plain,(
% 2.21/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f20])).
% 2.21/0.69  fof(f20,plain,(
% 2.21/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.21/0.69    inference(ennf_transformation,[],[f19])).
% 2.21/0.69  fof(f19,negated_conjecture,(
% 2.21/0.69    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 2.21/0.69    inference(negated_conjecture,[],[f18])).
% 2.21/0.69  fof(f18,conjecture,(
% 2.21/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).
% 2.21/0.69  fof(f3327,plain,(
% 2.21/0.69    ~l1_pre_topc(sK1) | (spl4_1 | ~spl4_23)),
% 2.21/0.69    inference(subsumption_resolution,[],[f3326,f58])).
% 2.21/0.69  fof(f58,plain,(
% 2.21/0.69    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f3326,plain,(
% 2.21/0.69    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | (spl4_1 | ~spl4_23)),
% 2.21/0.69    inference(subsumption_resolution,[],[f3314,f95])).
% 2.21/0.69  fof(f95,plain,(
% 2.21/0.69    ~v6_tops_1(sK3,sK1) | spl4_1),
% 2.21/0.69    inference(avatar_component_clause,[],[f93])).
% 2.21/0.69  fof(f93,plain,(
% 2.21/0.69    spl4_1 <=> v6_tops_1(sK3,sK1)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.21/0.69  fof(f3314,plain,(
% 2.21/0.69    v6_tops_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~spl4_23),
% 2.21/0.69    inference(trivial_inequality_removal,[],[f3312])).
% 2.21/0.69  fof(f3312,plain,(
% 2.21/0.69    sK3 != sK3 | v6_tops_1(sK3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~spl4_23),
% 2.21/0.69    inference(superposition,[],[f73,f253])).
% 2.21/0.69  fof(f253,plain,(
% 2.21/0.69    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~spl4_23),
% 2.21/0.69    inference(avatar_component_clause,[],[f251])).
% 2.21/0.69  fof(f251,plain,(
% 2.21/0.69    spl4_23 <=> sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.21/0.69  fof(f73,plain,(
% 2.21/0.69    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f48])).
% 2.21/0.69  fof(f48,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(nnf_transformation,[],[f28])).
% 2.21/0.69  fof(f28,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f11])).
% 2.21/0.69  fof(f11,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 2.21/0.69  fof(f3277,plain,(
% 2.21/0.69    spl4_22 | ~spl4_48 | ~spl4_69 | ~spl4_149),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f3276])).
% 2.21/0.69  fof(f3276,plain,(
% 2.21/0.69    $false | (spl4_22 | ~spl4_48 | ~spl4_69 | ~spl4_149)),
% 2.21/0.69    inference(subsumption_resolution,[],[f3275,f249])).
% 2.21/0.69  fof(f249,plain,(
% 2.21/0.69    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | spl4_22),
% 2.21/0.69    inference(avatar_component_clause,[],[f247])).
% 2.21/0.69  fof(f247,plain,(
% 2.21/0.69    spl4_22 <=> r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.21/0.69  fof(f3275,plain,(
% 2.21/0.69    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | (~spl4_48 | ~spl4_69 | ~spl4_149)),
% 2.21/0.69    inference(forward_demodulation,[],[f3274,f2195])).
% 2.21/0.69  fof(f2195,plain,(
% 2.21/0.69    sK3 = k1_tops_1(sK1,sK3) | (~spl4_48 | ~spl4_149)),
% 2.21/0.69    inference(forward_demodulation,[],[f2177,f354])).
% 2.21/0.69  fof(f354,plain,(
% 2.21/0.69    sK3 = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3))),
% 2.21/0.69    inference(backward_demodulation,[],[f191,f192])).
% 2.21/0.69  fof(f192,plain,(
% 2.21/0.69    k3_subset_1(u1_struct_0(sK1),sK3) = k4_xboole_0(u1_struct_0(sK1),sK3)),
% 2.21/0.69    inference(resolution,[],[f58,f79])).
% 2.21/0.69  fof(f79,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f32])).
% 2.21/0.69  fof(f32,plain,(
% 2.21/0.69    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.69    inference(ennf_transformation,[],[f3])).
% 2.21/0.69  fof(f3,axiom,(
% 2.21/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.21/0.69  fof(f191,plain,(
% 2.21/0.69    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))),
% 2.21/0.69    inference(resolution,[],[f58,f80])).
% 2.21/0.69  fof(f80,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.21/0.69    inference(cnf_transformation,[],[f33])).
% 2.21/0.69  fof(f33,plain,(
% 2.21/0.69    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.69    inference(ennf_transformation,[],[f4])).
% 2.21/0.69  fof(f4,axiom,(
% 2.21/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.21/0.69  fof(f2177,plain,(
% 2.21/0.69    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k4_xboole_0(u1_struct_0(sK1),sK3)) | (~spl4_48 | ~spl4_149)),
% 2.21/0.69    inference(backward_demodulation,[],[f1249,f1337])).
% 2.21/0.69  fof(f1337,plain,(
% 2.21/0.69    k4_xboole_0(u1_struct_0(sK1),sK3) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)) | ~spl4_149),
% 2.21/0.69    inference(avatar_component_clause,[],[f1335])).
% 2.21/0.69  fof(f1335,plain,(
% 2.21/0.69    spl4_149 <=> k4_xboole_0(u1_struct_0(sK1),sK3) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_149])])).
% 2.21/0.69  fof(f1249,plain,(
% 2.21/0.69    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3))) | ~spl4_48),
% 2.21/0.69    inference(backward_demodulation,[],[f457,f728])).
% 2.21/0.69  fof(f728,plain,(
% 2.21/0.69    k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)) | ~spl4_48),
% 2.21/0.69    inference(forward_demodulation,[],[f685,f457])).
% 2.21/0.69  fof(f685,plain,(
% 2.21/0.69    k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)))) | ~spl4_48),
% 2.21/0.69    inference(resolution,[],[f476,f80])).
% 2.21/0.69  fof(f476,plain,(
% 2.21/0.69    m1_subset_1(k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_48),
% 2.21/0.69    inference(avatar_component_clause,[],[f475])).
% 2.21/0.69  fof(f475,plain,(
% 2.21/0.69    spl4_48 <=> m1_subset_1(k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 2.21/0.69  fof(f457,plain,(
% 2.21/0.69    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)))),
% 2.21/0.69    inference(forward_demodulation,[],[f194,f192])).
% 2.21/0.69  fof(f194,plain,(
% 2.21/0.69    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))),
% 2.21/0.69    inference(subsumption_resolution,[],[f181,f56])).
% 2.21/0.69  fof(f181,plain,(
% 2.21/0.69    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) | ~l1_pre_topc(sK1)),
% 2.21/0.69    inference(resolution,[],[f58,f66])).
% 2.21/0.69  fof(f66,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f23])).
% 2.21/0.69  fof(f23,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f9])).
% 2.21/0.69  fof(f9,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 2.21/0.69  fof(f3274,plain,(
% 2.21/0.69    r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | (~spl4_48 | ~spl4_69 | ~spl4_149)),
% 2.21/0.69    inference(subsumption_resolution,[],[f3237,f193])).
% 2.21/0.69  fof(f193,plain,(
% 2.21/0.69    r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 2.21/0.69    inference(subsumption_resolution,[],[f180,f56])).
% 2.21/0.69  fof(f180,plain,(
% 2.21/0.69    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1)),
% 2.21/0.69    inference(resolution,[],[f58,f65])).
% 2.21/0.69  fof(f65,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f22])).
% 2.21/0.69  fof(f22,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f7])).
% 2.21/0.69  fof(f7,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.21/0.69  fof(f3237,plain,(
% 2.21/0.69    r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | (~spl4_48 | ~spl4_69 | ~spl4_149)),
% 2.21/0.69    inference(resolution,[],[f2562,f58])).
% 2.21/0.69  fof(f2562,plain,(
% 2.21/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~r1_tarski(X0,k2_pre_topc(sK1,sK3))) ) | (~spl4_48 | ~spl4_69 | ~spl4_149)),
% 2.21/0.69    inference(subsumption_resolution,[],[f2552,f56])).
% 2.21/0.69  fof(f2552,plain,(
% 2.21/0.69    ( ! [X0] : (~r1_tarski(X0,k2_pre_topc(sK1,sK3)) | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)) ) | (~spl4_48 | ~spl4_69 | ~spl4_149)),
% 2.21/0.69    inference(resolution,[],[f2247,f77])).
% 2.21/0.69  fof(f77,plain,(
% 2.21/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f31])).
% 2.21/0.69  fof(f31,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f30])).
% 2.21/0.69  fof(f30,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f16])).
% 2.21/0.69  fof(f16,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 2.21/0.69  fof(f2247,plain,(
% 2.21/0.69    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl4_48 | ~spl4_69 | ~spl4_149)),
% 2.21/0.69    inference(backward_demodulation,[],[f633,f2195])).
% 2.21/0.69  fof(f633,plain,(
% 2.21/0.69    m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_69),
% 2.21/0.69    inference(avatar_component_clause,[],[f631])).
% 2.21/0.69  fof(f631,plain,(
% 2.21/0.69    spl4_69 <=> m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 2.21/0.69  fof(f2427,plain,(
% 2.21/0.69    spl4_3 | ~spl4_9 | ~spl4_57 | ~spl4_194),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f2426])).
% 2.21/0.69  fof(f2426,plain,(
% 2.21/0.69    $false | (spl4_3 | ~spl4_9 | ~spl4_57 | ~spl4_194)),
% 2.21/0.69    inference(subsumption_resolution,[],[f2425,f103])).
% 2.21/0.69  fof(f103,plain,(
% 2.21/0.69    ~v4_tops_1(sK2,sK0) | spl4_3),
% 2.21/0.69    inference(avatar_component_clause,[],[f101])).
% 2.21/0.69  fof(f101,plain,(
% 2.21/0.69    spl4_3 <=> v4_tops_1(sK2,sK0)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.21/0.69  fof(f2425,plain,(
% 2.21/0.69    v4_tops_1(sK2,sK0) | (~spl4_9 | ~spl4_57 | ~spl4_194)),
% 2.21/0.69    inference(forward_demodulation,[],[f2367,f152])).
% 2.21/0.69  fof(f152,plain,(
% 2.21/0.69    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~spl4_9),
% 2.21/0.69    inference(avatar_component_clause,[],[f150])).
% 2.21/0.69  fof(f150,plain,(
% 2.21/0.69    spl4_9 <=> sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.21/0.69  fof(f2367,plain,(
% 2.21/0.69    v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) | (~spl4_9 | ~spl4_57 | ~spl4_194)),
% 2.21/0.69    inference(backward_demodulation,[],[f561,f1858])).
% 2.21/0.69  fof(f1858,plain,(
% 2.21/0.69    sK2 = k1_tops_1(sK0,sK2) | (~spl4_9 | ~spl4_194)),
% 2.21/0.69    inference(forward_demodulation,[],[f1857,f152])).
% 2.21/0.69  fof(f1857,plain,(
% 2.21/0.69    k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) | ~spl4_194),
% 2.21/0.69    inference(subsumption_resolution,[],[f1805,f55])).
% 2.21/0.69  fof(f55,plain,(
% 2.21/0.69    l1_pre_topc(sK0)),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f1805,plain,(
% 2.21/0.69    k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) | ~l1_pre_topc(sK0) | ~spl4_194),
% 2.21/0.69    inference(resolution,[],[f1781,f84])).
% 2.21/0.69  fof(f84,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f41])).
% 2.21/0.69  fof(f41,plain,(
% 2.21/0.69    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f40])).
% 2.21/0.69  fof(f40,plain,(
% 2.21/0.69    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.21/0.69    inference(ennf_transformation,[],[f14])).
% 2.21/0.69  fof(f14,axiom,(
% 2.21/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 2.21/0.69  fof(f1781,plain,(
% 2.21/0.69    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_194),
% 2.21/0.69    inference(avatar_component_clause,[],[f1780])).
% 2.21/0.69  fof(f1780,plain,(
% 2.21/0.69    spl4_194 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).
% 2.21/0.69  fof(f561,plain,(
% 2.21/0.69    v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),sK0) | ~spl4_57),
% 2.21/0.69    inference(avatar_component_clause,[],[f559])).
% 2.21/0.69  fof(f559,plain,(
% 2.21/0.69    spl4_57 <=> v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),sK0)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 2.21/0.69  fof(f1931,plain,(
% 2.21/0.69    ~spl4_35 | spl4_149 | ~spl4_33 | ~spl4_48),
% 2.21/0.69    inference(avatar_split_clause,[],[f1930,f475,f343,f1335,f366])).
% 2.21/0.69  fof(f366,plain,(
% 2.21/0.69    spl4_35 <=> v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 2.21/0.69  fof(f343,plain,(
% 2.21/0.69    spl4_33 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 2.21/0.69  fof(f1930,plain,(
% 2.21/0.69    k4_xboole_0(u1_struct_0(sK1),sK3) = k3_subset_1(u1_struct_0(sK1),k1_tops_1(sK1,sK3)) | ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | (~spl4_33 | ~spl4_48)),
% 2.21/0.69    inference(forward_demodulation,[],[f1929,f728])).
% 2.21/0.69  fof(f1929,plain,(
% 2.21/0.69    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) | ~spl4_33),
% 2.21/0.69    inference(subsumption_resolution,[],[f390,f56])).
% 2.21/0.69  fof(f390,plain,(
% 2.21/0.69    ~v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | k4_xboole_0(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)) | ~l1_pre_topc(sK1) | ~spl4_33),
% 2.21/0.69    inference(resolution,[],[f378,f68])).
% 2.21/0.69  fof(f68,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f26])).
% 2.21/0.69  fof(f26,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f25])).
% 2.21/0.69  fof(f25,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f8])).
% 2.21/0.69  fof(f8,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.21/0.69  fof(f378,plain,(
% 2.21/0.69    m1_subset_1(k4_xboole_0(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_33),
% 2.21/0.69    inference(forward_demodulation,[],[f344,f192])).
% 2.21/0.69  fof(f344,plain,(
% 2.21/0.69    m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_33),
% 2.21/0.69    inference(avatar_component_clause,[],[f343])).
% 2.21/0.69  fof(f1925,plain,(
% 2.21/0.69    spl4_35 | ~spl4_5 | ~spl4_33),
% 2.21/0.69    inference(avatar_split_clause,[],[f1924,f343,f111,f366])).
% 2.21/0.69  fof(f111,plain,(
% 2.21/0.69    spl4_5 <=> v3_pre_topc(sK3,sK1)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.21/0.69  fof(f1924,plain,(
% 2.21/0.69    ~v3_pre_topc(sK3,sK1) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | ~spl4_33),
% 2.21/0.69    inference(subsumption_resolution,[],[f1923,f56])).
% 2.21/0.69  fof(f1923,plain,(
% 2.21/0.69    ~v3_pre_topc(sK3,sK1) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | ~l1_pre_topc(sK1) | ~spl4_33),
% 2.21/0.69    inference(subsumption_resolution,[],[f435,f378])).
% 2.21/0.69  fof(f435,plain,(
% 2.21/0.69    ~v3_pre_topc(sK3,sK1) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK1),sK3),sK1) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 2.21/0.69    inference(superposition,[],[f71,f354])).
% 2.21/0.69  fof(f71,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f47])).
% 2.21/0.69  fof(f47,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(nnf_transformation,[],[f27])).
% 2.21/0.69  fof(f27,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f15])).
% 2.21/0.69  fof(f15,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 2.21/0.69  fof(f1856,plain,(
% 2.21/0.69    spl4_2 | ~spl4_9 | ~spl4_194),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f1855])).
% 2.21/0.69  fof(f1855,plain,(
% 2.21/0.69    $false | (spl4_2 | ~spl4_9 | ~spl4_194)),
% 2.21/0.69    inference(subsumption_resolution,[],[f1854,f99])).
% 2.21/0.69  fof(f99,plain,(
% 2.21/0.69    ~v3_pre_topc(sK2,sK0) | spl4_2),
% 2.21/0.69    inference(avatar_component_clause,[],[f97])).
% 2.21/0.69  fof(f97,plain,(
% 2.21/0.69    spl4_2 <=> v3_pre_topc(sK2,sK0)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.21/0.69  fof(f1854,plain,(
% 2.21/0.69    v3_pre_topc(sK2,sK0) | (~spl4_9 | ~spl4_194)),
% 2.21/0.69    inference(forward_demodulation,[],[f1853,f152])).
% 2.21/0.69  fof(f1853,plain,(
% 2.21/0.69    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) | ~spl4_194),
% 2.21/0.69    inference(subsumption_resolution,[],[f1852,f54])).
% 2.21/0.69  fof(f54,plain,(
% 2.21/0.69    v2_pre_topc(sK0)),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f1852,plain,(
% 2.21/0.69    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) | ~v2_pre_topc(sK0) | ~spl4_194),
% 2.21/0.69    inference(subsumption_resolution,[],[f1804,f55])).
% 2.21/0.69  fof(f1804,plain,(
% 2.21/0.69    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_194),
% 2.21/0.69    inference(resolution,[],[f1781,f81])).
% 2.21/0.69  fof(f81,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f35])).
% 2.21/0.69  fof(f35,plain,(
% 2.21/0.69    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f34])).
% 2.21/0.69  fof(f34,plain,(
% 2.21/0.69    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.21/0.69    inference(ennf_transformation,[],[f13])).
% 2.21/0.69  fof(f13,axiom,(
% 2.21/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.21/0.69  fof(f1792,plain,(
% 2.21/0.69    spl4_194),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f1791])).
% 2.21/0.69  fof(f1791,plain,(
% 2.21/0.69    $false | spl4_194),
% 2.21/0.69    inference(subsumption_resolution,[],[f1790,f55])).
% 2.21/0.69  fof(f1790,plain,(
% 2.21/0.69    ~l1_pre_topc(sK0) | spl4_194),
% 2.21/0.69    inference(subsumption_resolution,[],[f1788,f57])).
% 2.21/0.69  fof(f57,plain,(
% 2.21/0.69    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f1788,plain,(
% 2.21/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_194),
% 2.21/0.69    inference(resolution,[],[f1782,f82])).
% 2.21/0.69  fof(f82,plain,(
% 2.21/0.69    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f37])).
% 2.21/0.69  fof(f37,plain,(
% 2.21/0.69    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f36])).
% 2.21/0.69  fof(f36,plain,(
% 2.21/0.69    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.21/0.69    inference(ennf_transformation,[],[f6])).
% 2.21/0.69  fof(f6,axiom,(
% 2.21/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.21/0.69  fof(f1782,plain,(
% 2.21/0.69    ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_194),
% 2.21/0.69    inference(avatar_component_clause,[],[f1780])).
% 2.21/0.69  fof(f1482,plain,(
% 2.21/0.69    ~spl4_55 | ~spl4_56 | spl4_58),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f1481])).
% 2.21/0.69  fof(f1481,plain,(
% 2.21/0.69    $false | (~spl4_55 | ~spl4_56 | spl4_58)),
% 2.21/0.69    inference(subsumption_resolution,[],[f1480,f841])).
% 2.21/0.69  fof(f841,plain,(
% 2.21/0.69    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~spl4_55),
% 2.21/0.69    inference(forward_demodulation,[],[f840,f137])).
% 2.21/0.69  fof(f137,plain,(
% 2.21/0.69    k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))),
% 2.21/0.69    inference(subsumption_resolution,[],[f124,f55])).
% 2.21/0.69  fof(f124,plain,(
% 2.21/0.69    k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))) | ~l1_pre_topc(sK0)),
% 2.21/0.69    inference(resolution,[],[f57,f67])).
% 2.21/0.69  fof(f67,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f24])).
% 2.21/0.69  fof(f24,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f17])).
% 2.21/0.69  fof(f17,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k1_tops_1(X0,X1)) = k2_pre_topc(X0,k1_tops_1(X0,k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_tops_1)).
% 2.21/0.69  fof(f840,plain,(
% 2.21/0.69    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))) | ~spl4_55),
% 2.21/0.69    inference(subsumption_resolution,[],[f818,f55])).
% 2.21/0.69  fof(f818,plain,(
% 2.21/0.69    r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))) | ~l1_pre_topc(sK0) | ~spl4_55),
% 2.21/0.69    inference(resolution,[],[f549,f65])).
% 2.21/0.69  fof(f549,plain,(
% 2.21/0.69    m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_55),
% 2.21/0.69    inference(avatar_component_clause,[],[f548])).
% 2.21/0.69  fof(f548,plain,(
% 2.21/0.69    spl4_55 <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 2.21/0.69  fof(f1480,plain,(
% 2.21/0.69    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | (~spl4_56 | spl4_58)),
% 2.21/0.69    inference(forward_demodulation,[],[f1476,f137])).
% 2.21/0.69  fof(f1476,plain,(
% 2.21/0.69    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))) | (~spl4_56 | spl4_58)),
% 2.21/0.69    inference(backward_demodulation,[],[f565,f816])).
% 2.21/0.69  fof(f816,plain,(
% 2.21/0.69    k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))) | ~spl4_56),
% 2.21/0.69    inference(subsumption_resolution,[],[f764,f55])).
% 2.21/0.69  fof(f764,plain,(
% 2.21/0.69    k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))) | ~l1_pre_topc(sK0) | ~spl4_56),
% 2.21/0.69    inference(resolution,[],[f554,f84])).
% 2.21/0.69  fof(f554,plain,(
% 2.21/0.69    m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_56),
% 2.21/0.69    inference(avatar_component_clause,[],[f552])).
% 2.21/0.69  fof(f552,plain,(
% 2.21/0.69    spl4_56 <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 2.21/0.69  fof(f565,plain,(
% 2.21/0.69    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))))) | spl4_58),
% 2.21/0.69    inference(avatar_component_clause,[],[f563])).
% 2.21/0.69  fof(f563,plain,(
% 2.21/0.69    spl4_58 <=> r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))))))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 2.21/0.69  fof(f874,plain,(
% 2.21/0.69    spl4_68),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f873])).
% 2.21/0.69  fof(f873,plain,(
% 2.21/0.69    $false | spl4_68),
% 2.21/0.69    inference(subsumption_resolution,[],[f872,f56])).
% 2.21/0.69  fof(f872,plain,(
% 2.21/0.69    ~l1_pre_topc(sK1) | spl4_68),
% 2.21/0.69    inference(subsumption_resolution,[],[f870,f58])).
% 2.21/0.69  fof(f870,plain,(
% 2.21/0.69    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | spl4_68),
% 2.21/0.69    inference(resolution,[],[f869,f83])).
% 2.21/0.69  fof(f83,plain,(
% 2.21/0.69    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f39])).
% 2.21/0.69  fof(f39,plain,(
% 2.21/0.69    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f38])).
% 2.21/0.69  fof(f38,plain,(
% 2.21/0.69    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.21/0.69    inference(ennf_transformation,[],[f12])).
% 2.21/0.69  fof(f12,axiom,(
% 2.21/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 2.21/0.69  fof(f869,plain,(
% 2.21/0.69    ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl4_68),
% 2.21/0.69    inference(subsumption_resolution,[],[f867,f56])).
% 2.21/0.69  fof(f867,plain,(
% 2.21/0.69    ~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | spl4_68),
% 2.21/0.69    inference(resolution,[],[f745,f82])).
% 2.21/0.69  fof(f745,plain,(
% 2.21/0.69    ~m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | spl4_68),
% 2.21/0.69    inference(subsumption_resolution,[],[f743,f56])).
% 2.21/0.69  fof(f743,plain,(
% 2.21/0.69    ~m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | spl4_68),
% 2.21/0.69    inference(resolution,[],[f629,f83])).
% 2.21/0.69  fof(f629,plain,(
% 2.21/0.69    ~m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1))) | spl4_68),
% 2.21/0.69    inference(avatar_component_clause,[],[f627])).
% 2.21/0.69  fof(f627,plain,(
% 2.21/0.69    spl4_68 <=> m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 2.21/0.69  fof(f753,plain,(
% 2.21/0.69    spl4_55),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f752])).
% 2.21/0.69  fof(f752,plain,(
% 2.21/0.69    $false | spl4_55),
% 2.21/0.69    inference(subsumption_resolution,[],[f751,f55])).
% 2.21/0.69  fof(f751,plain,(
% 2.21/0.69    ~l1_pre_topc(sK0) | spl4_55),
% 2.21/0.69    inference(subsumption_resolution,[],[f749,f57])).
% 2.21/0.69  fof(f749,plain,(
% 2.21/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_55),
% 2.21/0.69    inference(resolution,[],[f748,f83])).
% 2.21/0.69  fof(f748,plain,(
% 2.21/0.69    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_55),
% 2.21/0.69    inference(subsumption_resolution,[],[f746,f55])).
% 2.21/0.69  fof(f746,plain,(
% 2.21/0.69    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_55),
% 2.21/0.69    inference(resolution,[],[f732,f82])).
% 2.21/0.69  fof(f732,plain,(
% 2.21/0.69    ~m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_55),
% 2.21/0.69    inference(subsumption_resolution,[],[f730,f55])).
% 2.21/0.69  fof(f730,plain,(
% 2.21/0.69    ~m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_55),
% 2.21/0.69    inference(resolution,[],[f550,f83])).
% 2.21/0.69  fof(f550,plain,(
% 2.21/0.69    ~m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_55),
% 2.21/0.69    inference(avatar_component_clause,[],[f548])).
% 2.21/0.69  fof(f656,plain,(
% 2.21/0.69    ~spl4_33 | spl4_48),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f655])).
% 2.21/0.69  fof(f655,plain,(
% 2.21/0.69    $false | (~spl4_33 | spl4_48)),
% 2.21/0.69    inference(subsumption_resolution,[],[f654,f56])).
% 2.21/0.69  fof(f654,plain,(
% 2.21/0.69    ~l1_pre_topc(sK1) | (~spl4_33 | spl4_48)),
% 2.21/0.69    inference(subsumption_resolution,[],[f652,f378])).
% 2.21/0.69  fof(f652,plain,(
% 2.21/0.69    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | spl4_48),
% 2.21/0.69    inference(resolution,[],[f477,f82])).
% 2.21/0.69  fof(f477,plain,(
% 2.21/0.69    ~m1_subset_1(k2_pre_topc(sK1,k4_xboole_0(u1_struct_0(sK1),sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | spl4_48),
% 2.21/0.69    inference(avatar_component_clause,[],[f475])).
% 2.21/0.69  fof(f634,plain,(
% 2.21/0.69    ~spl4_68 | spl4_69),
% 2.21/0.69    inference(avatar_split_clause,[],[f625,f631,f627])).
% 2.21/0.69  fof(f625,plain,(
% 2.21/0.69    m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1)))),
% 2.21/0.69    inference(subsumption_resolution,[],[f620,f56])).
% 2.21/0.69  fof(f620,plain,(
% 2.21/0.69    m1_subset_1(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 2.21/0.69    inference(superposition,[],[f82,f195])).
% 2.21/0.69  fof(f195,plain,(
% 2.21/0.69    k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))))),
% 2.21/0.69    inference(subsumption_resolution,[],[f182,f56])).
% 2.21/0.69  fof(f182,plain,(
% 2.21/0.69    k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) = k2_pre_topc(sK1,k1_tops_1(sK1,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))) | ~l1_pre_topc(sK1)),
% 2.21/0.69    inference(resolution,[],[f58,f67])).
% 2.21/0.69  fof(f566,plain,(
% 2.21/0.69    ~spl4_55 | spl4_57 | ~spl4_58),
% 2.21/0.69    inference(avatar_split_clause,[],[f557,f563,f559,f548])).
% 2.21/0.69  fof(f557,plain,(
% 2.21/0.69    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))))) | v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),sK0) | ~m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.69    inference(subsumption_resolution,[],[f556,f55])).
% 2.21/0.69  fof(f556,plain,(
% 2.21/0.69    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))))) | v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),sK0) | ~m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.21/0.69    inference(subsumption_resolution,[],[f542,f91])).
% 2.21/0.69  fof(f91,plain,(
% 2.21/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.21/0.69    inference(equality_resolution,[],[f85])).
% 2.21/0.69  fof(f85,plain,(
% 2.21/0.69    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.21/0.69    inference(cnf_transformation,[],[f52])).
% 2.21/0.69  fof(f52,plain,(
% 2.21/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.69    inference(flattening,[],[f51])).
% 2.21/0.69  fof(f51,plain,(
% 2.21/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.69    inference(nnf_transformation,[],[f1])).
% 2.21/0.69  fof(f1,axiom,(
% 2.21/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.21/0.69  fof(f542,plain,(
% 2.21/0.69    ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))) | ~r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k2_pre_topc(sK0,k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))))) | v4_tops_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),sK0) | ~m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.21/0.69    inference(superposition,[],[f76,f137])).
% 2.21/0.69  fof(f76,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f50])).
% 2.21/0.69  fof(f50,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(flattening,[],[f49])).
% 2.21/0.69  fof(f49,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(nnf_transformation,[],[f29])).
% 2.21/0.69  fof(f29,plain,(
% 2.21/0.69    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f10])).
% 2.21/0.69  fof(f10,axiom,(
% 2.21/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).
% 2.21/0.69  fof(f555,plain,(
% 2.21/0.69    ~spl4_55 | spl4_56),
% 2.21/0.69    inference(avatar_split_clause,[],[f546,f552,f548])).
% 2.21/0.69  fof(f546,plain,(
% 2.21/0.69    m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.21/0.69    inference(subsumption_resolution,[],[f541,f55])).
% 2.21/0.69  fof(f541,plain,(
% 2.21/0.69    m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.21/0.69    inference(superposition,[],[f82,f137])).
% 2.21/0.69  fof(f358,plain,(
% 2.21/0.69    spl4_33),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f357])).
% 2.21/0.69  fof(f357,plain,(
% 2.21/0.69    $false | spl4_33),
% 2.21/0.69    inference(subsumption_resolution,[],[f352,f78])).
% 2.21/0.69  fof(f78,plain,(
% 2.21/0.69    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f2])).
% 2.21/0.69  fof(f2,axiom,(
% 2.21/0.69    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.21/0.69  fof(f352,plain,(
% 2.21/0.69    ~r1_tarski(k4_xboole_0(u1_struct_0(sK1),sK3),u1_struct_0(sK1)) | spl4_33),
% 2.21/0.69    inference(backward_demodulation,[],[f351,f192])).
% 2.21/0.69  fof(f351,plain,(
% 2.21/0.69    ~r1_tarski(k3_subset_1(u1_struct_0(sK1),sK3),u1_struct_0(sK1)) | spl4_33),
% 2.21/0.69    inference(resolution,[],[f345,f89])).
% 2.21/0.69  fof(f89,plain,(
% 2.21/0.69    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f53])).
% 2.21/0.69  fof(f53,plain,(
% 2.21/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.21/0.69    inference(nnf_transformation,[],[f5])).
% 2.21/0.69  fof(f5,axiom,(
% 2.21/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.21/0.69  fof(f345,plain,(
% 2.21/0.69    ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | spl4_33),
% 2.21/0.69    inference(avatar_component_clause,[],[f343])).
% 2.21/0.69  fof(f254,plain,(
% 2.21/0.69    ~spl4_22 | spl4_23 | ~spl4_4),
% 2.21/0.69    inference(avatar_split_clause,[],[f245,f106,f251,f247])).
% 2.21/0.69  fof(f106,plain,(
% 2.21/0.69    spl4_4 <=> v4_tops_1(sK3,sK1)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.21/0.69  fof(f245,plain,(
% 2.21/0.69    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~spl4_4),
% 2.21/0.69    inference(resolution,[],[f207,f87])).
% 2.21/0.69  fof(f87,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f52])).
% 2.21/0.69  fof(f207,plain,(
% 2.21/0.69    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~spl4_4),
% 2.21/0.69    inference(subsumption_resolution,[],[f206,f56])).
% 2.21/0.69  fof(f206,plain,(
% 2.21/0.69    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1) | ~spl4_4),
% 2.21/0.69    inference(subsumption_resolution,[],[f185,f108])).
% 2.21/0.69  fof(f108,plain,(
% 2.21/0.69    v4_tops_1(sK3,sK1) | ~spl4_4),
% 2.21/0.69    inference(avatar_component_clause,[],[f106])).
% 2.21/0.69  fof(f185,plain,(
% 2.21/0.69    ~v4_tops_1(sK3,sK1) | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1)),
% 2.21/0.69    inference(resolution,[],[f58,f74])).
% 2.21/0.69  fof(f74,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tops_1(X1,X0) | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f50])).
% 2.21/0.69  fof(f153,plain,(
% 2.21/0.69    spl4_9 | ~spl4_6),
% 2.21/0.69    inference(avatar_split_clause,[],[f148,f116,f150])).
% 2.21/0.69  fof(f116,plain,(
% 2.21/0.69    spl4_6 <=> v6_tops_1(sK2,sK0)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.21/0.69  fof(f148,plain,(
% 2.21/0.69    ~v6_tops_1(sK2,sK0) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))),
% 2.21/0.69    inference(subsumption_resolution,[],[f126,f55])).
% 2.21/0.69  fof(f126,plain,(
% 2.21/0.69    ~v6_tops_1(sK2,sK0) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 2.21/0.69    inference(resolution,[],[f57,f72])).
% 2.21/0.69  fof(f72,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f48])).
% 2.21/0.69  fof(f121,plain,(
% 2.21/0.69    spl4_5 | spl4_6),
% 2.21/0.69    inference(avatar_split_clause,[],[f59,f116,f111])).
% 2.21/0.69  fof(f59,plain,(
% 2.21/0.69    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f120,plain,(
% 2.21/0.69    spl4_4 | spl4_6),
% 2.21/0.69    inference(avatar_split_clause,[],[f60,f116,f106])).
% 2.21/0.69  fof(f60,plain,(
% 2.21/0.69    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f119,plain,(
% 2.21/0.69    ~spl4_1 | spl4_6),
% 2.21/0.69    inference(avatar_split_clause,[],[f61,f116,f93])).
% 2.21/0.69  fof(f61,plain,(
% 2.21/0.69    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f114,plain,(
% 2.21/0.69    spl4_5 | ~spl4_2 | ~spl4_3),
% 2.21/0.69    inference(avatar_split_clause,[],[f62,f101,f97,f111])).
% 2.21/0.69  fof(f62,plain,(
% 2.21/0.69    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f109,plain,(
% 2.21/0.69    spl4_4 | ~spl4_2 | ~spl4_3),
% 2.21/0.69    inference(avatar_split_clause,[],[f63,f101,f97,f106])).
% 2.21/0.69  fof(f63,plain,(
% 2.21/0.69    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  fof(f104,plain,(
% 2.21/0.69    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 2.21/0.69    inference(avatar_split_clause,[],[f64,f101,f97,f93])).
% 2.21/0.69  fof(f64,plain,(
% 2.21/0.69    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 2.21/0.69    inference(cnf_transformation,[],[f46])).
% 2.21/0.69  % SZS output end Proof for theBenchmark
% 2.21/0.69  % (9223)------------------------------
% 2.21/0.69  % (9223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.69  % (9223)Termination reason: Refutation
% 2.21/0.69  
% 2.21/0.69  % (9223)Memory used [KB]: 12153
% 2.21/0.69  % (9223)Time elapsed: 0.250 s
% 2.21/0.69  % (9223)------------------------------
% 2.21/0.69  % (9223)------------------------------
% 2.21/0.70  % (9221)Success in time 0.33 s
%------------------------------------------------------------------------------
