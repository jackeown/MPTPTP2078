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
% DateTime   : Thu Dec  3 13:12:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 161 expanded)
%              Number of leaves         :   18 (  75 expanded)
%              Depth                    :    8
%              Number of atoms          :  245 ( 871 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10089)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f56,f61,f66,f71,f90,f102,f118])).

fof(f118,plain,
    ( ~ spl3_11
    | spl3_1
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f114,f63,f53,f33,f99])).

fof(f99,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f33,plain,
    ( spl3_1
  <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f53,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f63,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f114,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | spl3_1
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f65,f35,f72,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f72,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f55,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f35,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f102,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f97,f87,f68,f63,f58,f53,f48,f38,f99])).

fof(f38,plain,
    ( spl3_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,
    ( spl3_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f58,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f68,plain,
    ( spl3_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f87,plain,
    ( spl3_10
  <=> k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f97,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f96,f89])).

fof(f89,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f96,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f94,f75])).

fof(f75,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f60,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f60,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f94,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f70,f65,f40,f50,f60,f55,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f50,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f40,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f70,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f90,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f79,f63,f53,f43,f87])).

fof(f43,plain,
    ( spl3_3
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f65,f45,f55,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,
    ( v1_tops_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f71,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f19,f68])).

fof(f19,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v1_tops_1(X2,X0)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v1_tops_1(X2,sK0)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_pre_topc(X2,sK0)
            & v1_tops_1(X2,sK0)
            & v1_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_pre_topc(X2,sK0)
          & v1_tops_1(X2,sK0)
          & v1_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_pre_topc(X2,sK0)
        & v1_tops_1(X2,sK0)
        & v1_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_pre_topc(sK2,sK0)
      & v1_tops_1(sK2,sK0)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v1_tops_1(X2,X0)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

fof(f66,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f63])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f58])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f38])).

fof(f25,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f26,f33])).

fof(f26,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:44:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (10081)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.47  % (10081)Refutation not found, incomplete strategy% (10081)------------------------------
% 0.22/0.47  % (10081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (10081)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (10081)Memory used [KB]: 10490
% 0.22/0.47  % (10081)Time elapsed: 0.083 s
% 0.22/0.47  % (10081)------------------------------
% 0.22/0.47  % (10081)------------------------------
% 0.22/0.48  % (10084)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.48  % (10084)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (10092)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  % (10089)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f56,f61,f66,f71,f90,f102,f118])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ~spl3_11 | spl3_1 | ~spl3_5 | ~spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f114,f63,f53,f33,f99])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl3_11 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    spl3_1 <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    spl3_7 <=> l1_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    k2_struct_0(sK0) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | (spl3_1 | ~spl3_5 | ~spl3_7)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f65,f35,f72,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_5),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f55,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f53])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f33])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    l1_pre_topc(sK0) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f63])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    spl3_11 | ~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f97,f87,f68,f63,f58,f53,f48,f38,f99])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    spl3_2 <=> v3_pre_topc(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl3_4 <=> v1_tops_1(sK1,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl3_8 <=> v2_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl3_10 <=> k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_10)),
% 0.22/0.48    inference(forward_demodulation,[],[f96,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) | ~spl3_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f87])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.22/0.48    inference(forward_demodulation,[],[f94,f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_6),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f60,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f70,f65,f40,f50,f60,f55,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    v1_tops_1(sK1,sK0) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f48])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    v3_pre_topc(sK2,sK0) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f38])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    v2_pre_topc(sK0) | ~spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl3_10 | ~spl3_3 | ~spl3_5 | ~spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f79,f63,f53,f43,f87])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl3_3 <=> v1_tops_1(sK2,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) | (~spl3_3 | ~spl3_5 | ~spl3_7)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f65,f45,f55,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    v1_tops_1(sK2,sK0) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f43])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl3_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f68])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f16,f15,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f20,f63])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl3_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f21,f58])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    spl3_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f22,f53])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f23,f48])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    v1_tops_1(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f43])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    v1_tops_1(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f38])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    v3_pre_topc(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ~spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f33])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (10084)------------------------------
% 0.22/0.48  % (10084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (10084)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (10084)Memory used [KB]: 10618
% 0.22/0.48  % (10084)Time elapsed: 0.064 s
% 0.22/0.48  % (10084)------------------------------
% 0.22/0.48  % (10084)------------------------------
% 0.22/0.49  % (10077)Success in time 0.125 s
%------------------------------------------------------------------------------
