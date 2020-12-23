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
% DateTime   : Thu Dec  3 13:15:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 336 expanded)
%              Number of leaves         :   17 (  97 expanded)
%              Depth                    :   19
%              Number of atoms          :  235 (1188 expanded)
%              Number of equality atoms :   12 (  44 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f105,f173,f182])).

fof(f182,plain,(
    ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f169,f180])).

fof(f180,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_8 ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_8 ),
    inference(resolution,[],[f177,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

% (27580)Refutation not found, incomplete strategy% (27580)------------------------------
% (27580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

% (27580)Termination reason: Refutation not found, incomplete strategy

% (27580)Memory used [KB]: 6268
fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

% (27580)Time elapsed: 0.127 s
% (27580)------------------------------
% (27580)------------------------------
fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f177,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,k2_struct_0(sK0)),sK1)
        | r1_tarski(X0,k2_struct_0(sK0)) )
    | ~ spl3_8 ),
    inference(resolution,[],[f104,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k2_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f169,plain,(
    ~ r1_tarski(sK1,k2_struct_0(sK0)) ),
    inference(global_subsumption,[],[f39,f168])).

fof(f168,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(forward_demodulation,[],[f167,f54])).

fof(f54,plain,(
    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(global_subsumption,[],[f37,f53])).

fof(f53,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f36,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f167,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(forward_demodulation,[],[f166,f40])).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f166,plain,
    ( m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,k2_subset_1(k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f164,f40])).

fof(f164,plain,
    ( m2_connsp_2(k2_subset_1(k2_struct_0(sK0)),sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,k2_subset_1(k2_struct_0(sK0)))) ),
    inference(resolution,[],[f153,f41])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f153,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | m2_connsp_2(X1,sK0,sK1)
      | ~ r1_tarski(sK1,k1_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f84,f80])).

fof(f80,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f38,f77])).

fof(f77,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f55,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,k1_tops_1(sK0,X2))
      | m2_connsp_2(X2,sK0,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f36,f37,f82])).

fof(f82,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X3,k1_tops_1(sK0,X2))
      | m2_connsp_2(X2,sK0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f46,f77])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f39,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f173,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl3_1 ),
    inference(resolution,[],[f169,f106])).

fof(f106,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl3_1 ),
    inference(resolution,[],[f65,f49])).

fof(f65,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f64])).

% (27581)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f64,plain,
    ( spl3_1
  <=> ! [X2] : ~ r2_hidden(X2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f105,plain,
    ( spl3_5
    | spl3_8 ),
    inference(avatar_split_clause,[],[f100,f103,f89])).

fof(f89,plain,
    ( spl3_5
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f100,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | v1_xboole_0(k2_struct_0(sK0))
      | r2_hidden(X0,k2_struct_0(sK0)) ) ),
    inference(resolution,[],[f86,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f86,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k2_struct_0(sK0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f80,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f91,plain,
    ( spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f85,f89,f64])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f80,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:53:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (27603)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (27577)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (27580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (27585)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (27588)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (27576)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (27575)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (27583)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (27578)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (27577)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f183,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f91,f105,f173,f182])).
% 0.22/0.54  fof(f182,plain,(
% 0.22/0.54    ~spl3_8),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f181])).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    $false | ~spl3_8),
% 0.22/0.54    inference(subsumption_resolution,[],[f169,f180])).
% 0.22/0.54  fof(f180,plain,(
% 0.22/0.54    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl3_8),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f178])).
% 0.22/0.54  fof(f178,plain,(
% 0.22/0.54    r1_tarski(sK1,k2_struct_0(sK0)) | r1_tarski(sK1,k2_struct_0(sK0)) | ~spl3_8),
% 0.22/0.54    inference(resolution,[],[f177,f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  % (27580)Refutation not found, incomplete strategy% (27580)------------------------------
% 0.22/0.54  % (27580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 0.22/0.54  % (27580)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (27580)Memory used [KB]: 6268
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  % (27580)Time elapsed: 0.127 s
% 0.22/0.54  % (27580)------------------------------
% 0.22/0.54  % (27580)------------------------------
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f177,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(sK2(X0,k2_struct_0(sK0)),sK1) | r1_tarski(X0,k2_struct_0(sK0))) ) | ~spl3_8),
% 0.22/0.54    inference(resolution,[],[f104,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k2_struct_0(sK0)) | ~r2_hidden(X0,sK1)) ) | ~spl3_8),
% 0.22/0.54    inference(avatar_component_clause,[],[f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    spl3_8 <=> ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k2_struct_0(sK0)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ~r1_tarski(sK1,k2_struct_0(sK0))),
% 0.22/0.54    inference(global_subsumption,[],[f39,f168])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ~r1_tarski(sK1,k2_struct_0(sK0)) | m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f167,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.22/0.54    inference(global_subsumption,[],[f37,f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.22/0.54    inference(resolution,[],[f36,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f29,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.22/0.54    inference(forward_demodulation,[],[f166,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,k2_subset_1(k2_struct_0(sK0))))),
% 0.22/0.54    inference(forward_demodulation,[],[f164,f40])).
% 0.22/0.54  fof(f164,plain,(
% 0.22/0.54    m2_connsp_2(k2_subset_1(k2_struct_0(sK0)),sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,k2_subset_1(k2_struct_0(sK0))))),
% 0.22/0.54    inference(resolution,[],[f153,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.54  fof(f153,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | m2_connsp_2(X1,sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,X1))) )),
% 0.22/0.54    inference(resolution,[],[f84,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.54    inference(backward_demodulation,[],[f38,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f55,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    l1_struct_0(sK0)),
% 0.22/0.54    inference(resolution,[],[f37,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,k1_tops_1(sK0,X2)) | m2_connsp_2(X2,sK0,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.22/0.54    inference(global_subsumption,[],[f36,f37,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X3,k1_tops_1(sK0,X2)) | m2_connsp_2(X2,sK0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.22/0.54    inference(superposition,[],[f46,f77])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    ~spl3_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f170])).
% 0.22/0.54  fof(f170,plain,(
% 0.22/0.54    $false | ~spl3_1),
% 0.22/0.54    inference(resolution,[],[f169,f106])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl3_1),
% 0.22/0.54    inference(resolution,[],[f65,f49])).
% 0.22/0.54  fof(f65,plain,(
% 0.22/0.54    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl3_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f64])).
% 0.22/0.54  % (27581)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    spl3_1 <=> ! [X2] : ~r2_hidden(X2,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    spl3_5 | spl3_8),
% 0.22/0.54    inference(avatar_split_clause,[],[f100,f103,f89])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    spl3_5 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | v1_xboole_0(k2_struct_0(sK0)) | r2_hidden(X0,k2_struct_0(sK0))) )),
% 0.22/0.54    inference(resolution,[],[f86,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X1] : (m1_subset_1(X1,k2_struct_0(sK0)) | ~r2_hidden(X1,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f80,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    spl3_1 | ~spl3_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f85,f89,f64])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(k2_struct_0(sK0)) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f80,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (27577)------------------------------
% 0.22/0.54  % (27577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (27577)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (27577)Memory used [KB]: 10746
% 0.22/0.54  % (27577)Time elapsed: 0.130 s
% 0.22/0.54  % (27577)------------------------------
% 0.22/0.54  % (27577)------------------------------
% 0.22/0.54  % (27606)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (27570)Success in time 0.172 s
%------------------------------------------------------------------------------
