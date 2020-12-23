%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 449 expanded)
%              Number of leaves         :   22 ( 156 expanded)
%              Depth                    :   17
%              Number of atoms          :  335 (2010 expanded)
%              Number of equality atoms :   70 ( 380 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1465,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f134,f136,f171,f176,f195,f198,f299,f1398,f1464])).

fof(f1464,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f1451])).

fof(f1451,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f1449,f150])).

fof(f150,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl4_9
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1449,plain,
    ( r1_tarski(sK1,sK1)
    | spl4_9 ),
    inference(resolution,[],[f1438,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f1438,plain,
    ( ~ r2_hidden(sK3(sK1,sK1),sK1)
    | spl4_9 ),
    inference(resolution,[],[f150,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1398,plain,
    ( ~ spl4_9
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f1397])).

fof(f1397,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(trivial_inequality_removal,[],[f1394])).

fof(f1394,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2)
    | ~ spl4_9
    | ~ spl4_18 ),
    inference(superposition,[],[f219,f1320])).

fof(f1320,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1))
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f298,f1318])).

fof(f1318,plain,(
    sK2 = k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f862,f57])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f36,f55])).

fof(f55,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f54,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    & v3_pre_topc(sK2,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
              & v3_pre_topc(X2,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v1_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

% (19752)Refutation not found, incomplete strategy% (19752)------------------------------
% (19752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19752)Termination reason: Refutation not found, incomplete strategy

% (19752)Memory used [KB]: 10746
% (19752)Time elapsed: 0.140 s
% (19752)------------------------------
% (19752)------------------------------
fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
            & v3_pre_topc(X2,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v1_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
          & v3_pre_topc(X2,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
        & v3_pre_topc(X2,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
      & v3_pre_topc(sK2,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f862,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k9_subset_1(X2,X3,X2) = X3 ) ),
    inference(resolution,[],[f756,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f756,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k9_subset_1(X3,X2,X3) = X2 ) ),
    inference(superposition,[],[f518,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f518,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(condensation,[],[f511])).

fof(f511,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
      | k9_subset_1(X0,X2,X0) = k4_xboole_0(X2,k4_xboole_0(X2,X0)) ) ),
    inference(resolution,[],[f327,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f53,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f51,f44])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f327,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X0)
      | k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ) ),
    inference(resolution,[],[f211,f47])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X2,X0),X0)
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f61,f48])).

fof(f298,plain,
    ( k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl4_18
  <=> k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f219,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1))
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f58,f218])).

fof(f218,plain,
    ( ! [X3] : k9_subset_1(k2_struct_0(sK0),X3,sK1) = k9_subset_1(sK1,X3,sK1)
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f62,f214])).

fof(f214,plain,
    ( ! [X7] : k9_subset_1(sK1,X7,sK1) = k4_xboole_0(X7,k4_xboole_0(X7,sK1))
    | ~ spl4_9 ),
    inference(resolution,[],[f61,f151])).

fof(f151,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f62,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),X3,sK1) = k4_xboole_0(X3,k4_xboole_0(X3,sK1)) ),
    inference(resolution,[],[f53,f56])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f34,f55])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

% (19737)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f58,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    inference(backward_demodulation,[],[f38,f55])).

fof(f38,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f299,plain,
    ( ~ spl4_13
    | spl4_18
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f294,f193,f164,f149,f296,f168])).

fof(f168,plain,
    ( spl4_13
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f164,plain,
    ( spl4_12
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f193,plain,
    ( spl4_15
  <=> ! [X0] :
        ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

% (19740)Refutation not found, incomplete strategy% (19740)------------------------------
% (19740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19740)Termination reason: Refutation not found, incomplete strategy

% (19740)Memory used [KB]: 10746
% (19740)Time elapsed: 0.136 s
% (19740)------------------------------
% (19740)------------------------------
fof(f294,plain,
    ( k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f291,f218])).

fof(f291,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(superposition,[],[f194,f166])).

fof(f166,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f194,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f198,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl4_14 ),
    inference(resolution,[],[f191,f57])).

fof(f191,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl4_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f195,plain,
    ( ~ spl4_14
    | spl4_15
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f187,f132,f193,f189])).

fof(f132,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f187,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl4_8 ),
    inference(resolution,[],[f133,f37])).

fof(f37,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f176,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl4_13 ),
    inference(resolution,[],[f170,f56])).

fof(f170,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f171,plain,
    ( spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f162,f168,f164])).

fof(f162,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f79,f35])).

fof(f35,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(forward_demodulation,[],[f78,f55])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) ) ),
    inference(resolution,[],[f41,f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f136,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f130,f33])).

fof(f130,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f128])).

% (19754)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f128,plain,
    ( spl4_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f134,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f126,f132,f128])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f125,f55])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f124,f55])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f123,f55])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(resolution,[],[f43,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (19747)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.49  % (19735)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.49  % (19742)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (19759)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (19747)Refutation not found, incomplete strategy% (19747)------------------------------
% 0.20/0.51  % (19747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (19747)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (19747)Memory used [KB]: 10618
% 0.20/0.51  % (19747)Time elapsed: 0.094 s
% 0.20/0.51  % (19747)------------------------------
% 0.20/0.51  % (19747)------------------------------
% 0.20/0.51  % (19750)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (19730)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (19731)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (19753)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (19758)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (19743)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (19734)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (19732)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (19740)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (19733)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (19756)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (19751)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (19744)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (19757)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (19745)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (19748)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (19750)Refutation not found, incomplete strategy% (19750)------------------------------
% 0.20/0.54  % (19750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19750)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19750)Memory used [KB]: 10874
% 0.20/0.54  % (19750)Time elapsed: 0.145 s
% 0.20/0.54  % (19750)------------------------------
% 0.20/0.54  % (19750)------------------------------
% 0.20/0.54  % (19730)Refutation not found, incomplete strategy% (19730)------------------------------
% 0.20/0.54  % (19730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19730)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19730)Memory used [KB]: 1918
% 0.20/0.54  % (19730)Time elapsed: 0.112 s
% 0.20/0.54  % (19730)------------------------------
% 0.20/0.54  % (19730)------------------------------
% 0.20/0.54  % (19749)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (19752)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (19742)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (19734)Refutation not found, incomplete strategy% (19734)------------------------------
% 0.20/0.54  % (19734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19734)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19734)Memory used [KB]: 6268
% 0.20/0.54  % (19734)Time elapsed: 0.123 s
% 0.20/0.54  % (19734)------------------------------
% 0.20/0.54  % (19734)------------------------------
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f1465,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f134,f136,f171,f176,f195,f198,f299,f1398,f1464])).
% 0.20/0.54  fof(f1464,plain,(
% 0.20/0.54    spl4_9),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1451])).
% 0.20/0.54  fof(f1451,plain,(
% 0.20/0.54    $false | spl4_9),
% 0.20/0.54    inference(resolution,[],[f1449,f150])).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    ~r1_tarski(sK1,sK1) | spl4_9),
% 0.20/0.54    inference(avatar_component_clause,[],[f149])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    spl4_9 <=> r1_tarski(sK1,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.54  fof(f1449,plain,(
% 0.20/0.54    r1_tarski(sK1,sK1) | spl4_9),
% 0.20/0.54    inference(resolution,[],[f1438,f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f1438,plain,(
% 0.20/0.54    ~r2_hidden(sK3(sK1,sK1),sK1) | spl4_9),
% 0.20/0.54    inference(resolution,[],[f150,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f1398,plain,(
% 0.20/0.54    ~spl4_9 | ~spl4_18),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f1397])).
% 0.20/0.54  fof(f1397,plain,(
% 0.20/0.54    $false | (~spl4_9 | ~spl4_18)),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f1394])).
% 0.20/0.54  fof(f1394,plain,(
% 0.20/0.54    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,sK2) | (~spl4_9 | ~spl4_18)),
% 0.20/0.54    inference(superposition,[],[f219,f1320])).
% 0.20/0.54  fof(f1320,plain,(
% 0.20/0.54    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) | ~spl4_18),
% 0.20/0.54    inference(backward_demodulation,[],[f298,f1318])).
% 0.20/0.54  fof(f1318,plain,(
% 0.20/0.54    sK2 = k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))),
% 0.20/0.54    inference(resolution,[],[f862,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.54    inference(backward_demodulation,[],[f36,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.54    inference(resolution,[],[f54,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    l1_pre_topc(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ((k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f24,f23,f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  % (19752)Refutation not found, incomplete strategy% (19752)------------------------------
% 0.20/0.54  % (19752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19752)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19752)Memory used [KB]: 10746
% 0.20/0.54  % (19752)Time elapsed: 0.140 s
% 0.20/0.54  % (19752)------------------------------
% 0.20/0.54  % (19752)------------------------------
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,negated_conjecture,(
% 0.20/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.20/0.54    inference(negated_conjecture,[],[f10])).
% 0.20/0.54  fof(f10,conjecture,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.55    inference(resolution,[],[f39,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f862,plain,(
% 0.20/0.55    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k9_subset_1(X2,X3,X2) = X3) )),
% 0.20/0.55    inference(resolution,[],[f756,f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.55    inference(nnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.55  fof(f756,plain,(
% 0.20/0.55    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k9_subset_1(X3,X2,X3) = X2) )),
% 0.20/0.55    inference(superposition,[],[f518,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(definition_unfolding,[],[f45,f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.55  fof(f518,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.55    inference(condensation,[],[f511])).
% 0.20/0.55  fof(f511,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) | k9_subset_1(X0,X2,X0) = k4_xboole_0(X2,k4_xboole_0(X2,X0))) )),
% 0.20/0.55    inference(resolution,[],[f327,f61])).
% 0.20/0.55  fof(f61,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.20/0.55    inference(resolution,[],[f53,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f51,f44])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.55  fof(f327,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X0) | k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.55    inference(resolution,[],[f211,f47])).
% 0.20/0.55  fof(f211,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X2,X0),X0) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.20/0.55    inference(resolution,[],[f61,f48])).
% 0.20/0.55  fof(f298,plain,(
% 0.20/0.55    k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) | ~spl4_18),
% 0.20/0.55    inference(avatar_component_clause,[],[f296])).
% 0.20/0.55  fof(f296,plain,(
% 0.20/0.55    spl4_18 <=> k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.55  fof(f219,plain,(
% 0.20/0.55    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) | ~spl4_9),
% 0.20/0.55    inference(backward_demodulation,[],[f58,f218])).
% 0.20/0.55  fof(f218,plain,(
% 0.20/0.55    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),X3,sK1) = k9_subset_1(sK1,X3,sK1)) ) | ~spl4_9),
% 0.20/0.55    inference(backward_demodulation,[],[f62,f214])).
% 0.20/0.55  fof(f214,plain,(
% 0.20/0.55    ( ! [X7] : (k9_subset_1(sK1,X7,sK1) = k4_xboole_0(X7,k4_xboole_0(X7,sK1))) ) | ~spl4_9),
% 0.20/0.55    inference(resolution,[],[f61,f151])).
% 0.20/0.55  fof(f151,plain,(
% 0.20/0.55    r1_tarski(sK1,sK1) | ~spl4_9),
% 0.20/0.55    inference(avatar_component_clause,[],[f149])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),X3,sK1) = k4_xboole_0(X3,k4_xboole_0(X3,sK1))) )),
% 0.20/0.55    inference(resolution,[],[f53,f56])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    inference(backward_demodulation,[],[f34,f55])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  % (19737)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 0.20/0.55    inference(backward_demodulation,[],[f38,f55])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f299,plain,(
% 0.20/0.55    ~spl4_13 | spl4_18 | ~spl4_9 | ~spl4_12 | ~spl4_15),
% 0.20/0.55    inference(avatar_split_clause,[],[f294,f193,f164,f149,f296,f168])).
% 0.20/0.55  fof(f168,plain,(
% 0.20/0.55    spl4_13 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.55  fof(f164,plain,(
% 0.20/0.55    spl4_12 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.55  fof(f193,plain,(
% 0.20/0.55    spl4_15 <=> ! [X0] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.55  % (19740)Refutation not found, incomplete strategy% (19740)------------------------------
% 0.20/0.55  % (19740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (19740)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (19740)Memory used [KB]: 10746
% 0.20/0.55  % (19740)Time elapsed: 0.136 s
% 0.20/0.55  % (19740)------------------------------
% 0.20/0.55  % (19740)------------------------------
% 0.20/0.55  fof(f294,plain,(
% 0.20/0.55    k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_9 | ~spl4_12 | ~spl4_15)),
% 0.20/0.55    inference(forward_demodulation,[],[f291,f218])).
% 0.20/0.55  fof(f291,plain,(
% 0.20/0.55    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl4_12 | ~spl4_15)),
% 0.20/0.55    inference(superposition,[],[f194,f166])).
% 0.20/0.55  fof(f166,plain,(
% 0.20/0.55    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~spl4_12),
% 0.20/0.55    inference(avatar_component_clause,[],[f164])).
% 0.20/0.55  fof(f194,plain,(
% 0.20/0.55    ( ! [X0] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl4_15),
% 0.20/0.55    inference(avatar_component_clause,[],[f193])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    spl4_14),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f196])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    $false | spl4_14),
% 0.20/0.55    inference(resolution,[],[f191,f57])).
% 0.20/0.55  fof(f191,plain,(
% 0.20/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | spl4_14),
% 0.20/0.55    inference(avatar_component_clause,[],[f189])).
% 0.20/0.55  fof(f189,plain,(
% 0.20/0.55    spl4_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.55  fof(f195,plain,(
% 0.20/0.55    ~spl4_14 | spl4_15 | ~spl4_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f187,f132,f193,f189])).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    spl4_8 <=> ! [X1,X0] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.55  fof(f187,plain,(
% 0.20/0.55    ( ! [X0] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl4_8),
% 0.20/0.55    inference(resolution,[],[f133,f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    v3_pre_topc(sK2,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) ) | ~spl4_8),
% 0.20/0.55    inference(avatar_component_clause,[],[f132])).
% 0.20/0.55  fof(f176,plain,(
% 0.20/0.55    spl4_13),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f174])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    $false | spl4_13),
% 0.20/0.55    inference(resolution,[],[f170,f56])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | spl4_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f168])).
% 0.20/0.55  fof(f171,plain,(
% 0.20/0.55    spl4_12 | ~spl4_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f162,f168,f164])).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.55    inference(resolution,[],[f79,f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    v1_tops_1(sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f78,f55])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)) )),
% 0.20/0.55    inference(resolution,[],[f41,f33])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.55  fof(f136,plain,(
% 0.20/0.55    spl4_7),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    $false | spl4_7),
% 0.20/0.55    inference(resolution,[],[f130,f33])).
% 0.20/0.55  fof(f130,plain,(
% 0.20/0.55    ~l1_pre_topc(sK0) | spl4_7),
% 0.20/0.55    inference(avatar_component_clause,[],[f128])).
% 0.20/0.55  % (19754)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    spl4_7 <=> l1_pre_topc(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    ~spl4_7 | spl4_8),
% 0.20/0.55    inference(avatar_split_clause,[],[f126,f132,f128])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f125,f55])).
% 0.20/0.55  fof(f125,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f124,f55])).
% 0.20/0.55  fof(f124,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 0.20/0.55    inference(forward_demodulation,[],[f123,f55])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 0.20/0.55    inference(resolution,[],[f43,f32])).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    v2_pre_topc(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f25])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (19742)------------------------------
% 0.20/0.55  % (19742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (19742)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (19742)Memory used [KB]: 7036
% 0.20/0.55  % (19742)Time elapsed: 0.121 s
% 0.20/0.55  % (19742)------------------------------
% 0.20/0.55  % (19742)------------------------------
% 0.20/0.55  % (19725)Success in time 0.187 s
%------------------------------------------------------------------------------
