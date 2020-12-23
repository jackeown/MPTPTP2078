%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1388+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  154 (2443 expanded)
%              Number of leaves         :   21 ( 793 expanded)
%              Depth                    :   25
%              Number of atoms          :  690 (15758 expanded)
%              Number of equality atoms :   61 ( 405 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f601,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f400,f405,f410,f415,f421,f589])).

fof(f589,plain,
    ( ~ spl5_32
    | ~ spl5_33
    | spl5_34
    | ~ spl5_35 ),
    inference(avatar_contradiction_clause,[],[f588])).

fof(f588,plain,
    ( $false
    | ~ spl5_32
    | ~ spl5_33
    | spl5_34
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f587,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r3_connsp_1(sK0,sK2,sK1)
    & r1_tarski(sK1,sK2)
    & v3_connsp_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_connsp_1(X0,X2,X1)
                & r1_tarski(X1,X2)
                & v3_connsp_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(sK0,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r3_connsp_1(sK0,X2,X1)
            & r1_tarski(X1,X2)
            & v3_connsp_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r3_connsp_1(sK0,X2,sK1)
          & r1_tarski(sK1,X2)
          & v3_connsp_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ~ r3_connsp_1(sK0,X2,sK1)
        & r1_tarski(sK1,X2)
        & v3_connsp_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r3_connsp_1(sK0,sK2,sK1)
      & r1_tarski(sK1,sK2)
      & v3_connsp_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(X0,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_connsp_1(X0,X2,X1)
              & r1_tarski(X1,X2)
              & v3_connsp_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X1,X2)
                    & v3_connsp_1(X1,X0) )
                 => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( r1_tarski(X1,X2)
                    & v3_connsp_1(X1,X0) )
                 => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_connsp_1(X1,X0) )
               => r3_connsp_1(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_connsp_2)).

fof(f587,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_32
    | ~ spl5_33
    | spl5_34
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f586,f47])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f586,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_32
    | ~ spl5_33
    | spl5_34
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f585,f49])).

fof(f49,plain,(
    v3_connsp_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f585,plain,
    ( ~ v3_connsp_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_32
    | ~ spl5_33
    | spl5_34
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f574,f568])).

fof(f568,plain,
    ( v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),sK0)
    | ~ spl5_32
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f567,f45])).

% (5865)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f567,plain,
    ( v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_32
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f566,f46])).

fof(f566,plain,
    ( v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_32
    | ~ spl5_33 ),
    inference(resolution,[],[f435,f93])).

fof(f93,plain,(
    m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f91,f46])).

fof(f91,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK2),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f71,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f435,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK2),X0)
        | v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_32
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f433,f404])).

fof(f404,plain,
    ( m1_subset_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(sK2))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl5_33
  <=> m1_subset_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f433,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(sK2))
        | v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK2),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_32 ),
    inference(resolution,[],[f399,f264])).

fof(f264,plain,(
    ! [X12,X11] :
      ( ~ v2_connsp_1(X11,k1_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X11,k1_zfmisc_1(sK2))
      | v2_connsp_1(X11,X12)
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK2),X12)
      | ~ l1_pre_topc(X12)
      | ~ v2_pre_topc(X12) ) ),
    inference(superposition,[],[f79,f186])).

fof(f186,plain,(
    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(forward_demodulation,[],[f185,f164])).

fof(f164,plain,(
    sK2 = k2_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f163,f46])).

fof(f163,plain,
    ( sK2 = k2_struct_0(k1_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f162,f48])).

fof(f162,plain,
    ( sK2 = k2_struct_0(k1_pre_topc(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f160,f88])).

fof(f88,plain,(
    v1_pre_topc(k1_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f86,f46])).

fof(f86,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f70,f48])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f160,plain,
    ( sK2 = k2_struct_0(k1_pre_topc(sK0,sK2))
    | ~ v1_pre_topc(k1_pre_topc(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f93,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f185,plain,(
    k2_struct_0(k1_pre_topc(sK0,sK2)) = u1_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f168,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f168,plain,(
    l1_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f165,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f165,plain,(
    l1_pre_topc(k1_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f161,f46])).

fof(f161,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_connsp_1(X3,X1)
      | v2_connsp_1(X3,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f77,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( v2_connsp_1(X3,X0)
      | ~ v2_connsp_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_connsp_1(X2,X0)
      | ~ v2_connsp_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_connsp_1(X2,X0)
                      | ~ v2_connsp_1(X3,X1) )
                    & ( v2_connsp_1(X3,X1)
                      | ~ v2_connsp_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_connsp_1(X2,X0)
                    <=> v2_connsp_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_connsp_1)).

fof(f399,plain,
    ( v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_pre_topc(sK0,sK2))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl5_32
  <=> v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f574,plain,
    ( ~ v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),sK0)
    | ~ v3_connsp_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_33
    | spl5_34
    | ~ spl5_35 ),
    inference(resolution,[],[f484,f424])).

fof(f424,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),X0)
        | ~ v3_connsp_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | spl5_34
    | ~ spl5_35 ),
    inference(subsumption_resolution,[],[f422,f409])).

fof(f409,plain,
    ( sK1 != sK3(k1_pre_topc(sK0,sK2),sK1)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f407])).

fof(f407,plain,
    ( spl5_34
  <=> sK1 = sK3(k1_pre_topc(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f422,plain,
    ( ! [X0] :
        ( sK1 = sK3(k1_pre_topc(sK0,sK2),sK1)
        | ~ v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),X0)
        | ~ m1_subset_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_connsp_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_35 ),
    inference(resolution,[],[f414,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X1,X3)
      | X1 = X3
      | ~ v2_connsp_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_connsp_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ( sK3(X0,X1) != X1
                & r1_tarski(X1,sK3(X0,X1))
                & v2_connsp_1(sK3(X0,X1),X0)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_connsp_1(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_connsp_1(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != X1
        & r1_tarski(X1,sK3(X0,X1))
        & v2_connsp_1(sK3(X0,X1),X0)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_connsp_1(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_connsp_1(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_connsp_1(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_connsp_1(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_connsp_1(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_connsp_1(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_connsp_1(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_connsp_1(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_connsp_1(X1,X0) )
              | ~ v3_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_connsp_1(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_connsp_1(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_connsp_1(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_connsp_1(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_connsp_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_connsp_1(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_connsp_1(X2,X0) )
                   => X1 = X2 ) )
              & v2_connsp_1(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_connsp_1)).

fof(f414,plain,
    ( r1_tarski(sK1,sK3(k1_pre_topc(sK0,sK2),sK1))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl5_35
  <=> r1_tarski(sK1,sK3(k1_pre_topc(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f484,plain,
    ( m1_subset_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f474,f46])).

fof(f474,plain,
    ( m1_subset_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_33 ),
    inference(resolution,[],[f425,f93])).

fof(f425,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK2),X0)
        | m1_subset_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_33 ),
    inference(resolution,[],[f404,f255])).

fof(f255,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK2))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK2),X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f55,f186])).

fof(f421,plain,(
    ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f419,f47])).

fof(f419,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f418,f51])).

fof(f51,plain,(
    ~ r3_connsp_1(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f418,plain,
    ( r3_connsp_1(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f416,f84])).

fof(f84,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f73,f50])).

fof(f50,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

% (5860)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f416,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | r3_connsp_1(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_20 ),
    inference(resolution,[],[f289,f270])).

fof(f270,plain,(
    ! [X0] :
      ( ~ v3_connsp_1(X0,k1_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | r3_connsp_1(sK0,sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f269,f46])).

fof(f269,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | ~ v3_connsp_1(X0,k1_pre_topc(sK0,sK2))
      | r3_connsp_1(sK0,sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f254,f48])).

fof(f254,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
      | ~ v3_connsp_1(X0,k1_pre_topc(sK0,sK2))
      | r3_connsp_1(sK0,sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f74,f186])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
      | r3_connsp_1(X0,X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_connsp_1(X0,X1,X2)
      | ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_connsp_1(X0,X1,X2)
                  | ! [X3] :
                      ( ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                & ( ( v3_connsp_1(sK4(X0,X1,X2),k1_pre_topc(X0,X1))
                    & sK4(X0,X1,X2) = X2
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                  | ~ r3_connsp_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( v3_connsp_1(X4,k1_pre_topc(X0,X1))
          & X2 = X4
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
     => ( v3_connsp_1(sK4(X0,X1,X2),k1_pre_topc(X0,X1))
        & sK4(X0,X1,X2) = X2
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_connsp_1(X0,X1,X2)
                  | ! [X3] :
                      ( ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                & ( ? [X4] :
                      ( v3_connsp_1(X4,k1_pre_topc(X0,X1))
                      & X2 = X4
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                  | ~ r3_connsp_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_connsp_1(X0,X1,X2)
                  | ! [X3] :
                      ( ~ v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
                & ( ? [X3] :
                      ( v3_connsp_1(X3,k1_pre_topc(X0,X1))
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) )
                  | ~ r3_connsp_1(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_connsp_1(X0,X1,X2)
              <=> ? [X3] :
                    ( v3_connsp_1(X3,k1_pre_topc(X0,X1))
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) )
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
             => ( r3_connsp_1(X0,X1,X2)
              <=> ? [X3] :
                    ( v3_connsp_1(X3,k1_pre_topc(X0,X1))
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X1)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_connsp_1)).

fof(f289,plain,
    ( v3_connsp_1(sK1,k1_pre_topc(sK0,sK2))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl5_20
  <=> v3_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f415,plain,
    ( spl5_20
    | spl5_35 ),
    inference(avatar_split_clause,[],[f340,f412,f288])).

fof(f340,plain,
    ( r1_tarski(sK1,sK3(k1_pre_topc(sK0,sK2),sK1))
    | v3_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f339,f84])).

fof(f339,plain,
    ( r1_tarski(sK1,sK3(k1_pre_topc(sK0,sK2),sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | v3_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f274,f280])).

fof(f280,plain,(
    v2_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f279,f93])).

fof(f279,plain,
    ( v2_connsp_1(sK1,k1_pre_topc(sK0,sK2))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) ),
    inference(subsumption_resolution,[],[f265,f84])).

fof(f265,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | v2_connsp_1(sK1,k1_pre_topc(sK0,sK2))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK2),sK0) ),
    inference(superposition,[],[f121,f186])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_connsp_1(sK1,X0)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f120,f45])).

fof(f120,plain,(
    ! [X0] :
      ( v2_connsp_1(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f46])).

fof(f119,plain,(
    ! [X0] :
      ( v2_connsp_1(sK1,X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f80,f97])).

fof(f97,plain,(
    v2_connsp_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f96,f46])).

fof(f96,plain,
    ( v2_connsp_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f94,f49])).

fof(f94,plain,
    ( ~ v3_connsp_1(sK1,sK0)
    | v2_connsp_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f56,f47])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_connsp_1(X1,X0)
      | v2_connsp_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_connsp_1(X3,X0)
      | v2_connsp_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f78,f55])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( v2_connsp_1(X3,X1)
      | ~ v2_connsp_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_connsp_1(X3,X1)
      | ~ v2_connsp_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f274,plain,(
    ! [X6] :
      ( ~ v2_connsp_1(X6,k1_pre_topc(sK0,sK2))
      | r1_tarski(X6,sK3(k1_pre_topc(sK0,sK2),X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK2))
      | v3_connsp_1(X6,k1_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f259,f165])).

% (5856)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f259,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK2))
      | r1_tarski(X6,sK3(k1_pre_topc(sK0,sK2),X6))
      | ~ v2_connsp_1(X6,k1_pre_topc(sK0,sK2))
      | v3_connsp_1(X6,k1_pre_topc(sK0,sK2))
      | ~ l1_pre_topc(k1_pre_topc(sK0,sK2)) ) ),
    inference(superposition,[],[f60,f186])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,sK3(X0,X1))
      | ~ v2_connsp_1(X1,X0)
      | v3_connsp_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f410,plain,
    ( spl5_20
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f344,f407,f288])).

fof(f344,plain,
    ( sK1 != sK3(k1_pre_topc(sK0,sK2),sK1)
    | v3_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f343,f84])).

fof(f343,plain,
    ( sK1 != sK3(k1_pre_topc(sK0,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | v3_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f275,f280])).

fof(f275,plain,(
    ! [X7] :
      ( ~ v2_connsp_1(X7,k1_pre_topc(sK0,sK2))
      | sK3(k1_pre_topc(sK0,sK2),X7) != X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK2))
      | v3_connsp_1(X7,k1_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f260,f165])).

fof(f260,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(sK2))
      | sK3(k1_pre_topc(sK0,sK2),X7) != X7
      | ~ v2_connsp_1(X7,k1_pre_topc(sK0,sK2))
      | v3_connsp_1(X7,k1_pre_topc(sK0,sK2))
      | ~ l1_pre_topc(k1_pre_topc(sK0,sK2)) ) ),
    inference(superposition,[],[f61,f186])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sK3(X0,X1) != X1
      | ~ v2_connsp_1(X1,X0)
      | v3_connsp_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f405,plain,
    ( spl5_20
    | spl5_33 ),
    inference(avatar_split_clause,[],[f347,f402,f288])).

fof(f347,plain,
    ( m1_subset_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(sK2))
    | v3_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f346,f84])).

fof(f346,plain,
    ( m1_subset_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | v3_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f272,f280])).

fof(f272,plain,(
    ! [X4] :
      ( ~ v2_connsp_1(X4,k1_pre_topc(sK0,sK2))
      | m1_subset_1(sK3(k1_pre_topc(sK0,sK2),X4),k1_zfmisc_1(sK2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK2))
      | v3_connsp_1(X4,k1_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f257,f165])).

fof(f257,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(sK2))
      | m1_subset_1(sK3(k1_pre_topc(sK0,sK2),X4),k1_zfmisc_1(sK2))
      | ~ v2_connsp_1(X4,k1_pre_topc(sK0,sK2))
      | v3_connsp_1(X4,k1_pre_topc(sK0,sK2))
      | ~ l1_pre_topc(k1_pre_topc(sK0,sK2)) ) ),
    inference(superposition,[],[f58,f186])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_connsp_1(X1,X0)
      | v3_connsp_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f400,plain,
    ( spl5_20
    | spl5_32 ),
    inference(avatar_split_clause,[],[f350,f397,f288])).

fof(f350,plain,
    ( v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_pre_topc(sK0,sK2))
    | v3_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f349,f84])).

fof(f349,plain,
    ( v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),sK1),k1_pre_topc(sK0,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | v3_connsp_1(sK1,k1_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f273,f280])).

fof(f273,plain,(
    ! [X5] :
      ( ~ v2_connsp_1(X5,k1_pre_topc(sK0,sK2))
      | v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),X5),k1_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X5,k1_zfmisc_1(sK2))
      | v3_connsp_1(X5,k1_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f258,f165])).

fof(f258,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(sK2))
      | v2_connsp_1(sK3(k1_pre_topc(sK0,sK2),X5),k1_pre_topc(sK0,sK2))
      | ~ v2_connsp_1(X5,k1_pre_topc(sK0,sK2))
      | v3_connsp_1(X5,k1_pre_topc(sK0,sK2))
      | ~ l1_pre_topc(k1_pre_topc(sK0,sK2)) ) ),
    inference(superposition,[],[f59,f186])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_connsp_1(sK3(X0,X1),X0)
      | ~ v2_connsp_1(X1,X0)
      | v3_connsp_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

%------------------------------------------------------------------------------
