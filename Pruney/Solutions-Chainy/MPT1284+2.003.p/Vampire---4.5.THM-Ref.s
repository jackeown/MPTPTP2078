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
% DateTime   : Thu Dec  3 13:13:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 491 expanded)
%              Number of leaves         :   22 ( 207 expanded)
%              Depth                    :   19
%              Number of atoms          :  508 (4585 expanded)
%              Number of equality atoms :   39 (  60 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f565,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f93,f94,f172,f180,f501,f539,f564])).

fof(f564,plain,
    ( spl4_3
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f563])).

fof(f563,plain,
    ( $false
    | spl4_3
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f562,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

% (26126)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f562,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl4_3
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f561,f176])).

fof(f176,plain,
    ( sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl4_11
  <=> sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f561,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | spl4_3
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f560,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v4_pre_topc(sK2,sK0) )
        & v5_tops_1(sK2,sK0) )
      | ( ~ v5_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v4_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v4_pre_topc(X2,X0) )
                        & v5_tops_1(X2,X0) )
                      | ( ~ v5_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v4_pre_topc(X2,sK0) )
                      & v5_tops_1(X2,sK0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK0)
                      | ~ v4_pre_topc(X2,sK0) )
                    & v5_tops_1(X2,sK0) )
                  | ( ~ v5_tops_1(X3,X1)
                    & v4_tops_1(X3,X1)
                    & v4_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK0)
                    | ~ v4_pre_topc(X2,sK0) )
                  & v5_tops_1(X2,sK0) )
                | ( ~ v5_tops_1(X3,sK1)
                  & v4_tops_1(X3,sK1)
                  & v4_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK0)
                  | ~ v4_pre_topc(X2,sK0) )
                & v5_tops_1(X2,sK0) )
              | ( ~ v5_tops_1(X3,sK1)
                & v4_tops_1(X3,sK1)
                & v4_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK2,sK0)
                | ~ v4_pre_topc(sK2,sK0) )
              & v5_tops_1(sK2,sK0) )
            | ( ~ v5_tops_1(X3,sK1)
              & v4_tops_1(X3,sK1)
              & v4_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK2,sK0)
              | ~ v4_pre_topc(sK2,sK0) )
            & v5_tops_1(sK2,sK0) )
          | ( ~ v5_tops_1(X3,sK1)
            & v4_tops_1(X3,sK1)
            & v4_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ( ~ v4_tops_1(sK2,sK0)
            | ~ v4_pre_topc(sK2,sK0) )
          & v5_tops_1(sK2,sK0) )
        | ( ~ v5_tops_1(sK3,sK1)
          & v4_tops_1(sK3,sK1)
          & v4_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v5_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v4_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v4_pre_topc(X3,X1) )
                       => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v5_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v4_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) )
                     => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).

fof(f560,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ l1_pre_topc(sK0)
    | spl4_3
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f559,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f559,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_3
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f558,f76])).

fof(f76,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_3
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f558,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f549,f531])).

fof(f531,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f196,f176])).

fof(f196,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f186,f38])).

fof(f186,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f116,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f116,plain,(
    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f114,f38])).

fof(f114,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f549,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(superposition,[],[f55,f528])).

fof(f528,plain,
    ( sK2 = k2_pre_topc(sK0,sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f241,f176])).

fof(f241,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f195,f38])).

fof(f195,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f116,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(f539,plain,
    ( spl4_2
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | spl4_2
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f532,f72])).

fof(f72,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_2
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f532,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl4_11 ),
    inference(superposition,[],[f239,f176])).

fof(f239,plain,(
    v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f238,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f238,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f193,f38])).

fof(f193,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f116,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f501,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f499,f311])).

fof(f311,plain,
    ( ~ r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f310,f139])).

% (26142)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f139,plain,
    ( sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f138,f39])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f138,plain,
    ( sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | ~ l1_pre_topc(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f135,f68])).

fof(f68,plain,
    ( ~ v5_tops_1(sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_1
  <=> v5_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f135,plain,
    ( sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | v5_tops_1(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f52,f41])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f310,plain,
    ( sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3))
    | ~ r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f148,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f148,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f147,f39])).

fof(f147,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f146,f81])).

fof(f81,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_4
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f146,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f54,f41])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tops_1(X1,X0)
      | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f499,plain,
    ( r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3)
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f498,f169])).

fof(f169,plain,
    ( sK3 = k2_pre_topc(sK1,sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl4_10
  <=> sK3 = k2_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f498,plain,
    ( r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k2_pre_topc(sK1,sK3))
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f497,f39])).

fof(f497,plain,
    ( r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f496,f41])).

fof(f496,plain,
    ( r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k2_pre_topc(sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(resolution,[],[f297,f117])).

fof(f117,plain,(
    m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f115,f39])).

fof(f115,plain,
    ( m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f58,f41])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(X0)))
        | r1_tarski(k2_pre_topc(X0,k1_tops_1(sK1,sK3)),k2_pre_topc(X0,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f296,f169])).

fof(f296,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(X0,k1_tops_1(sK1,sK3)),k2_pre_topc(X0,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f294,f169])).

fof(f294,plain,
    ( ! [X0] :
        ( r1_tarski(k2_pre_topc(X0,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),k2_pre_topc(X0,sK3))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f143,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f143,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f142,f39])).

fof(f142,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f141,f81])).

fof(f141,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f53,f41])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tops_1(X1,X0)
      | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f180,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f179,f89,f175])).

fof(f89,plain,
    ( spl4_6
  <=> v5_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f179,plain,
    ( ~ v5_tops_1(sK2,sK0)
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f132,f38])).

fof(f132,plain,
    ( ~ v5_tops_1(sK2,sK0)
    | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f51,f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f172,plain,
    ( spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f171,f84,f167])).

fof(f84,plain,
    ( spl4_5
  <=> v4_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f171,plain,
    ( ~ v4_pre_topc(sK3,sK1)
    | sK3 = k2_pre_topc(sK1,sK3) ),
    inference(subsumption_resolution,[],[f119,f39])).

fof(f119,plain,
    ( ~ v4_pre_topc(sK3,sK1)
    | sK3 = k2_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f49,f41])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f94,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f42,f89,f84])).

fof(f42,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f93,plain,
    ( spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f43,f89,f79])).

fof(f43,plain,
    ( v5_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,
    ( ~ spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f44,f89,f66])).

fof(f44,plain,
    ( v5_tops_1(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,
    ( spl4_5
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f45,f74,f70,f84])).

fof(f45,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,
    ( spl4_4
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f46,f74,f70,f79])).

fof(f46,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f47,f74,f70,f66])).

fof(f47,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v4_pre_topc(sK2,sK0)
    | ~ v5_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:39:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (26128)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (26121)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (26124)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (26123)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (26129)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (26140)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (26130)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (26139)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (26141)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (26119)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (26133)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (26132)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (26129)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (26135)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (26143)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (26125)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (26144)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.52  % (26127)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.52  % (26137)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (26120)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.36/0.54  % (26122)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.36/0.54  % (26131)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f565,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f93,f94,f172,f180,f501,f539,f564])).
% 1.36/0.54  fof(f564,plain,(
% 1.36/0.54    spl4_3 | ~spl4_11),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f563])).
% 1.36/0.54  fof(f563,plain,(
% 1.36/0.54    $false | (spl4_3 | ~spl4_11)),
% 1.36/0.54    inference(subsumption_resolution,[],[f562,f63])).
% 1.36/0.54  fof(f63,plain,(
% 1.36/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.36/0.54    inference(equality_resolution,[],[f61])).
% 1.36/0.54  fof(f61,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.36/0.54    inference(cnf_transformation,[],[f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.54    inference(flattening,[],[f35])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.36/0.54    inference(nnf_transformation,[],[f1])).
% 1.36/0.54  % (26126)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.36/0.54  fof(f562,plain,(
% 1.36/0.54    ~r1_tarski(sK2,sK2) | (spl4_3 | ~spl4_11)),
% 1.36/0.54    inference(forward_demodulation,[],[f561,f176])).
% 1.36/0.54  fof(f176,plain,(
% 1.36/0.54    sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | ~spl4_11),
% 1.36/0.54    inference(avatar_component_clause,[],[f175])).
% 1.36/0.54  fof(f175,plain,(
% 1.36/0.54    spl4_11 <=> sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.36/0.54  fof(f561,plain,(
% 1.36/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | (spl4_3 | ~spl4_11)),
% 1.36/0.54    inference(subsumption_resolution,[],[f560,f38])).
% 1.36/0.54  fof(f38,plain,(
% 1.36/0.54    l1_pre_topc(sK0)),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ((((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v4_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f30,f29,f28,f27])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f29,plain,(
% 1.36/0.54    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v4_pre_topc(X2,sK0)) & v5_tops_1(X2,sK0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    ? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v4_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((((~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0)) & v5_tops_1(sK2,sK0)) | (~v5_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v4_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f13,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f12])).
% 1.36/0.54  fof(f12,plain,(
% 1.36/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f11])).
% 1.36/0.54  fof(f11,negated_conjecture,(
% 1.36/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 1.36/0.54    inference(negated_conjecture,[],[f10])).
% 1.36/0.54  fof(f10,conjecture,(
% 1.36/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).
% 1.36/0.54  fof(f560,plain,(
% 1.36/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~l1_pre_topc(sK0) | (spl4_3 | ~spl4_11)),
% 1.36/0.54    inference(subsumption_resolution,[],[f559,f40])).
% 1.36/0.54  fof(f40,plain,(
% 1.36/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f559,plain,(
% 1.36/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_3 | ~spl4_11)),
% 1.36/0.54    inference(subsumption_resolution,[],[f558,f76])).
% 1.36/0.54  fof(f76,plain,(
% 1.36/0.54    ~v4_tops_1(sK2,sK0) | spl4_3),
% 1.36/0.54    inference(avatar_component_clause,[],[f74])).
% 1.36/0.54  fof(f74,plain,(
% 1.36/0.54    spl4_3 <=> v4_tops_1(sK2,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.36/0.54  fof(f558,plain,(
% 1.36/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_11),
% 1.36/0.54    inference(subsumption_resolution,[],[f549,f531])).
% 1.36/0.54  fof(f531,plain,(
% 1.36/0.54    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl4_11),
% 1.36/0.54    inference(superposition,[],[f196,f176])).
% 1.36/0.54  fof(f196,plain,(
% 1.36/0.54    r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))),
% 1.36/0.54    inference(subsumption_resolution,[],[f186,f38])).
% 1.36/0.54  fof(f186,plain,(
% 1.36/0.54    r1_tarski(k1_tops_1(sK0,sK2),k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~l1_pre_topc(sK0)),
% 1.36/0.54    inference(resolution,[],[f116,f48])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.36/0.54  fof(f116,plain,(
% 1.36/0.54    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.36/0.54    inference(subsumption_resolution,[],[f114,f38])).
% 1.36/0.54  fof(f114,plain,(
% 1.36/0.54    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.36/0.54    inference(resolution,[],[f58,f40])).
% 1.36/0.54  fof(f58,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f24])).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f23])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,axiom,(
% 1.36/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.36/0.54  fof(f549,plain,(
% 1.36/0.54    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_11),
% 1.36/0.54    inference(superposition,[],[f55,f528])).
% 1.36/0.54  fof(f528,plain,(
% 1.36/0.54    sK2 = k2_pre_topc(sK0,sK2) | ~spl4_11),
% 1.36/0.54    inference(superposition,[],[f241,f176])).
% 1.36/0.54  fof(f241,plain,(
% 1.36/0.54    k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))),
% 1.36/0.54    inference(subsumption_resolution,[],[f195,f38])).
% 1.36/0.54  fof(f195,plain,(
% 1.36/0.54    k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~l1_pre_topc(sK0)),
% 1.36/0.54    inference(resolution,[],[f116,f59])).
% 1.36/0.54  fof(f59,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f26])).
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f25])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f2])).
% 1.36/0.54  fof(f2,axiom,(
% 1.36/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 1.36/0.54  fof(f55,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f34,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f33])).
% 1.36/0.54  fof(f33,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(nnf_transformation,[],[f18])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).
% 1.36/0.54  fof(f539,plain,(
% 1.36/0.54    spl4_2 | ~spl4_11),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f538])).
% 1.36/0.54  fof(f538,plain,(
% 1.36/0.54    $false | (spl4_2 | ~spl4_11)),
% 1.36/0.54    inference(subsumption_resolution,[],[f532,f72])).
% 1.36/0.54  fof(f72,plain,(
% 1.36/0.54    ~v4_pre_topc(sK2,sK0) | spl4_2),
% 1.36/0.54    inference(avatar_component_clause,[],[f70])).
% 1.36/0.54  fof(f70,plain,(
% 1.36/0.54    spl4_2 <=> v4_pre_topc(sK2,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.36/0.54  fof(f532,plain,(
% 1.36/0.54    v4_pre_topc(sK2,sK0) | ~spl4_11),
% 1.36/0.54    inference(superposition,[],[f239,f176])).
% 1.36/0.54  fof(f239,plain,(
% 1.36/0.54    v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0)),
% 1.36/0.54    inference(subsumption_resolution,[],[f238,f37])).
% 1.36/0.54  fof(f37,plain,(
% 1.36/0.54    v2_pre_topc(sK0)),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f238,plain,(
% 1.36/0.54    v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) | ~v2_pre_topc(sK0)),
% 1.36/0.54    inference(subsumption_resolution,[],[f193,f38])).
% 1.36/0.54  fof(f193,plain,(
% 1.36/0.54    v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK2)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.36/0.54    inference(resolution,[],[f116,f57])).
% 1.36/0.54  fof(f57,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f22])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f21])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.36/0.54    inference(ennf_transformation,[],[f9])).
% 1.36/0.54  fof(f9,axiom,(
% 1.36/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.36/0.54  fof(f501,plain,(
% 1.36/0.54    spl4_1 | ~spl4_4 | ~spl4_10),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f500])).
% 1.36/0.54  fof(f500,plain,(
% 1.36/0.54    $false | (spl4_1 | ~spl4_4 | ~spl4_10)),
% 1.36/0.54    inference(subsumption_resolution,[],[f499,f311])).
% 1.36/0.54  fof(f311,plain,(
% 1.36/0.54    ~r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) | (spl4_1 | ~spl4_4)),
% 1.36/0.54    inference(subsumption_resolution,[],[f310,f139])).
% 1.36/0.54  % (26142)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.36/0.54  fof(f139,plain,(
% 1.36/0.54    sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | spl4_1),
% 1.36/0.54    inference(subsumption_resolution,[],[f138,f39])).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    l1_pre_topc(sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f138,plain,(
% 1.36/0.54    sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | ~l1_pre_topc(sK1) | spl4_1),
% 1.36/0.54    inference(subsumption_resolution,[],[f135,f68])).
% 1.36/0.54  fof(f68,plain,(
% 1.36/0.54    ~v5_tops_1(sK3,sK1) | spl4_1),
% 1.36/0.54    inference(avatar_component_clause,[],[f66])).
% 1.36/0.54  fof(f66,plain,(
% 1.36/0.54    spl4_1 <=> v5_tops_1(sK3,sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.36/0.54  fof(f135,plain,(
% 1.36/0.54    sK3 != k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | v5_tops_1(sK3,sK1) | ~l1_pre_topc(sK1)),
% 1.36/0.54    inference(resolution,[],[f52,f41])).
% 1.36/0.54  fof(f41,plain,(
% 1.36/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f52,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | v5_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f32])).
% 1.36/0.54  fof(f32,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(nnf_transformation,[],[f17])).
% 1.36/0.54  fof(f17,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).
% 1.36/0.54  fof(f310,plain,(
% 1.36/0.54    sK3 = k2_pre_topc(sK1,k1_tops_1(sK1,sK3)) | ~r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) | ~spl4_4),
% 1.36/0.54    inference(resolution,[],[f148,f62])).
% 1.36/0.54  fof(f62,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f36])).
% 1.36/0.54  fof(f148,plain,(
% 1.36/0.54    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~spl4_4),
% 1.36/0.54    inference(subsumption_resolution,[],[f147,f39])).
% 1.36/0.54  fof(f147,plain,(
% 1.36/0.54    r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~l1_pre_topc(sK1) | ~spl4_4),
% 1.36/0.54    inference(subsumption_resolution,[],[f146,f81])).
% 1.36/0.54  fof(f81,plain,(
% 1.36/0.54    v4_tops_1(sK3,sK1) | ~spl4_4),
% 1.36/0.54    inference(avatar_component_clause,[],[f79])).
% 1.36/0.54  fof(f79,plain,(
% 1.36/0.54    spl4_4 <=> v4_tops_1(sK3,sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.36/0.54  fof(f146,plain,(
% 1.36/0.54    ~v4_tops_1(sK3,sK1) | r1_tarski(sK3,k2_pre_topc(sK1,k1_tops_1(sK1,sK3))) | ~l1_pre_topc(sK1)),
% 1.36/0.54    inference(resolution,[],[f54,f41])).
% 1.36/0.54  fof(f54,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tops_1(X1,X0) | r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f499,plain,(
% 1.36/0.54    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),sK3) | (~spl4_4 | ~spl4_10)),
% 1.36/0.54    inference(forward_demodulation,[],[f498,f169])).
% 1.36/0.54  fof(f169,plain,(
% 1.36/0.54    sK3 = k2_pre_topc(sK1,sK3) | ~spl4_10),
% 1.36/0.54    inference(avatar_component_clause,[],[f167])).
% 1.36/0.54  fof(f167,plain,(
% 1.36/0.54    spl4_10 <=> sK3 = k2_pre_topc(sK1,sK3)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.36/0.54  fof(f498,plain,(
% 1.36/0.54    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k2_pre_topc(sK1,sK3)) | (~spl4_4 | ~spl4_10)),
% 1.36/0.54    inference(subsumption_resolution,[],[f497,f39])).
% 1.36/0.54  fof(f497,plain,(
% 1.36/0.54    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1) | (~spl4_4 | ~spl4_10)),
% 1.36/0.54    inference(subsumption_resolution,[],[f496,f41])).
% 1.36/0.54  fof(f496,plain,(
% 1.36/0.54    r1_tarski(k2_pre_topc(sK1,k1_tops_1(sK1,sK3)),k2_pre_topc(sK1,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | (~spl4_4 | ~spl4_10)),
% 1.36/0.54    inference(resolution,[],[f297,f117])).
% 1.36/0.54  fof(f117,plain,(
% 1.36/0.54    m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.36/0.54    inference(subsumption_resolution,[],[f115,f39])).
% 1.36/0.54  fof(f115,plain,(
% 1.36/0.54    m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.36/0.54    inference(resolution,[],[f58,f41])).
% 1.36/0.54  fof(f297,plain,(
% 1.36/0.54    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK1,sK3),k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k2_pre_topc(X0,k1_tops_1(sK1,sK3)),k2_pre_topc(X0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | (~spl4_4 | ~spl4_10)),
% 1.36/0.54    inference(forward_demodulation,[],[f296,f169])).
% 1.36/0.54  fof(f296,plain,(
% 1.36/0.54    ( ! [X0] : (r1_tarski(k2_pre_topc(X0,k1_tops_1(sK1,sK3)),k2_pre_topc(X0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | (~spl4_4 | ~spl4_10)),
% 1.36/0.54    inference(forward_demodulation,[],[f294,f169])).
% 1.36/0.54  fof(f294,plain,(
% 1.36/0.54    ( ! [X0] : (r1_tarski(k2_pre_topc(X0,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))),k2_pre_topc(X0,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl4_4),
% 1.36/0.54    inference(resolution,[],[f143,f56])).
% 1.36/0.54  fof(f56,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f20])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f19])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_pre_topc)).
% 1.36/0.54  fof(f143,plain,(
% 1.36/0.54    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~spl4_4),
% 1.36/0.54    inference(subsumption_resolution,[],[f142,f39])).
% 1.36/0.54  fof(f142,plain,(
% 1.36/0.54    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1) | ~spl4_4),
% 1.36/0.54    inference(subsumption_resolution,[],[f141,f81])).
% 1.36/0.54  fof(f141,plain,(
% 1.36/0.54    ~v4_tops_1(sK3,sK1) | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1)),
% 1.36/0.54    inference(resolution,[],[f53,f41])).
% 1.36/0.54  fof(f53,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tops_1(X1,X0) | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f34])).
% 1.36/0.54  fof(f180,plain,(
% 1.36/0.54    spl4_11 | ~spl4_6),
% 1.36/0.54    inference(avatar_split_clause,[],[f179,f89,f175])).
% 1.36/0.54  fof(f89,plain,(
% 1.36/0.54    spl4_6 <=> v5_tops_1(sK2,sK0)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.36/0.54  fof(f179,plain,(
% 1.36/0.54    ~v5_tops_1(sK2,sK0) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2))),
% 1.36/0.54    inference(subsumption_resolution,[],[f132,f38])).
% 1.36/0.54  fof(f132,plain,(
% 1.36/0.54    ~v5_tops_1(sK2,sK0) | sK2 = k2_pre_topc(sK0,k1_tops_1(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 1.36/0.54    inference(resolution,[],[f51,f40])).
% 1.36/0.54  fof(f51,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f32])).
% 1.36/0.54  fof(f172,plain,(
% 1.36/0.54    spl4_10 | ~spl4_5),
% 1.36/0.54    inference(avatar_split_clause,[],[f171,f84,f167])).
% 1.36/0.54  fof(f84,plain,(
% 1.36/0.54    spl4_5 <=> v4_pre_topc(sK3,sK1)),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.36/0.54  fof(f171,plain,(
% 1.36/0.54    ~v4_pre_topc(sK3,sK1) | sK3 = k2_pre_topc(sK1,sK3)),
% 1.36/0.54    inference(subsumption_resolution,[],[f119,f39])).
% 1.36/0.54  fof(f119,plain,(
% 1.36/0.54    ~v4_pre_topc(sK3,sK1) | sK3 = k2_pre_topc(sK1,sK3) | ~l1_pre_topc(sK1)),
% 1.36/0.54    inference(resolution,[],[f49,f41])).
% 1.36/0.54  fof(f49,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f16])).
% 1.36/0.54  fof(f16,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(flattening,[],[f15])).
% 1.36/0.54  fof(f15,plain,(
% 1.36/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.36/0.54  fof(f94,plain,(
% 1.36/0.54    spl4_5 | spl4_6),
% 1.36/0.54    inference(avatar_split_clause,[],[f42,f89,f84])).
% 1.36/0.54  fof(f42,plain,(
% 1.36/0.54    v5_tops_1(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f93,plain,(
% 1.36/0.54    spl4_4 | spl4_6),
% 1.36/0.54    inference(avatar_split_clause,[],[f43,f89,f79])).
% 1.36/0.54  fof(f43,plain,(
% 1.36/0.54    v5_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f92,plain,(
% 1.36/0.54    ~spl4_1 | spl4_6),
% 1.36/0.54    inference(avatar_split_clause,[],[f44,f89,f66])).
% 1.36/0.54  fof(f44,plain,(
% 1.36/0.54    v5_tops_1(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f87,plain,(
% 1.36/0.54    spl4_5 | ~spl4_2 | ~spl4_3),
% 1.36/0.54    inference(avatar_split_clause,[],[f45,f74,f70,f84])).
% 1.36/0.54  fof(f45,plain,(
% 1.36/0.54    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_pre_topc(sK3,sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f82,plain,(
% 1.36/0.54    spl4_4 | ~spl4_2 | ~spl4_3),
% 1.36/0.54    inference(avatar_split_clause,[],[f46,f74,f70,f79])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  fof(f77,plain,(
% 1.36/0.54    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.36/0.54    inference(avatar_split_clause,[],[f47,f74,f70,f66])).
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    ~v4_tops_1(sK2,sK0) | ~v4_pre_topc(sK2,sK0) | ~v5_tops_1(sK3,sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f31])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (26129)------------------------------
% 1.36/0.54  % (26129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (26129)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (26129)Memory used [KB]: 10874
% 1.36/0.54  % (26129)Time elapsed: 0.098 s
% 1.36/0.54  % (26129)------------------------------
% 1.36/0.54  % (26129)------------------------------
% 1.36/0.54  % (26116)Success in time 0.182 s
%------------------------------------------------------------------------------
