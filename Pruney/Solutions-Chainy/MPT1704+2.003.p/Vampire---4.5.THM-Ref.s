%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:42 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  180 (2318 expanded)
%              Number of leaves         :   23 ( 697 expanded)
%              Depth                    :   31
%              Number of atoms          :  751 (26707 expanded)
%              Number of equality atoms :   50 (2081 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8916)Termination reason: Refutation not found, incomplete strategy

% (8916)Memory used [KB]: 10874
% (8916)Time elapsed: 0.179 s
% (8916)------------------------------
% (8916)------------------------------
fof(f950,plain,(
    $false ),
    inference(subsumption_resolution,[],[f949,f906])).

fof(f906,plain,(
    v1_borsuk_1(sK1,sK0) ),
    inference(resolution,[],[f883,f244])).

fof(f244,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK1),sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f243,f68])).

fof(f68,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_borsuk_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_borsuk_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_borsuk_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_borsuk_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f52,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_borsuk_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ v1_borsuk_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_borsuk_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_borsuk_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_borsuk_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK0)
              | ~ v1_borsuk_1(X2,sK0)
              | ~ m1_pre_topc(X1,sK0)
              | ~ v1_borsuk_1(X1,sK0) )
            & ( ( m1_pre_topc(X2,sK0)
                & v1_borsuk_1(X2,sK0) )
              | ( m1_pre_topc(X1,sK0)
                & v1_borsuk_1(X1,sK0) ) )
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK0)
            | ~ v1_borsuk_1(X2,sK0)
            | ~ m1_pre_topc(sK1,sK0)
            | ~ v1_borsuk_1(sK1,sK0) )
          & ( ( m1_pre_topc(X2,sK0)
              & v1_borsuk_1(X2,sK0) )
            | ( m1_pre_topc(sK1,sK0)
              & v1_borsuk_1(sK1,sK0) ) )
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK0)
          | ~ v1_borsuk_1(X2,sK0)
          | ~ m1_pre_topc(sK1,sK0)
          | ~ v1_borsuk_1(sK1,sK0) )
        & ( ( m1_pre_topc(X2,sK0)
            & v1_borsuk_1(X2,sK0) )
          | ( m1_pre_topc(sK1,sK0)
            & v1_borsuk_1(sK1,sK0) ) )
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK2,sK0)
        | ~ v1_borsuk_1(sK2,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_borsuk_1(sK1,sK0) )
      & ( ( m1_pre_topc(sK2,sK0)
          & v1_borsuk_1(sK2,sK0) )
        | ( m1_pre_topc(sK1,sK0)
          & v1_borsuk_1(sK1,sK0) ) )
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_borsuk_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_borsuk_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_borsuk_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tmap_1)).

fof(f243,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK1),sK0)
    | v1_borsuk_1(sK1,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f239,f69])).

fof(f69,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f239,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK1),sK0)
    | v1_borsuk_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f217,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f119,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ v4_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ v4_pre_topc(X2,X0) )
                & ( v4_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

% (8914)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (8923)Refutation not found, incomplete strategy% (8923)------------------------------
% (8923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

fof(f217,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f215,f69])).

fof(f215,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f180,f78])).

fof(f78,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f180,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f179,f72])).

fof(f72,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f179,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f178,f70])).

fof(f70,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f178,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(sK1)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f177,f71])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f177,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f129,f74])).

fof(f74,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f53])).

fof(f129,plain,(
    ! [X2,X0] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f117,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f117,plain,(
    ! [X2,X0] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f883,plain,(
    v4_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f761,f302])).

fof(f302,plain,
    ( ~ v1_borsuk_1(sK1,sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f301,f217])).

fof(f301,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f299,f246])).

fof(f246,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(forward_demodulation,[],[f245,f74])).

fof(f245,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f240,f69])).

fof(f240,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f217,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f299,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(resolution,[],[f210,f79])).

fof(f79,plain,
    ( ~ v1_borsuk_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f210,plain,
    ( v1_borsuk_1(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f209,f203])).

fof(f203,plain,
    ( v4_pre_topc(u1_struct_0(sK2),sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f202,f168])).

fof(f168,plain,
    ( m1_pre_topc(sK1,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0) ),
    inference(subsumption_resolution,[],[f167,f78])).

fof(f167,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f166,f68])).

fof(f166,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ v2_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f163,f69])).

fof(f163,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f131,f76])).

fof(f76,plain,
    ( v1_borsuk_1(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f125,f88])).

fof(f125,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f202,plain,
    ( v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f201,f68])).

fof(f201,plain,
    ( v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f200,f69])).

fof(f200,plain,
    ( v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f171,f131])).

fof(f171,plain,
    ( v1_borsuk_1(sK1,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0) ),
    inference(subsumption_resolution,[],[f170,f77])).

fof(f77,plain,
    ( v1_borsuk_1(sK1,sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f170,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f169,f68])).

fof(f169,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ v2_pre_topc(sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f164,f69])).

fof(f164,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(resolution,[],[f131,f75])).

fof(f75,plain,
    ( v1_borsuk_1(sK2,sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f209,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK2),sK0)
    | v1_borsuk_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f208,f68])).

fof(f208,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK2),sK0)
    | v1_borsuk_1(sK2,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f204,f69])).

fof(f204,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK2),sK0)
    | v1_borsuk_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f174,f130])).

fof(f174,plain,
    ( m1_pre_topc(sK2,sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f173,f78])).

fof(f173,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f172,f68])).

fof(f172,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f165,f69])).

fof(f165,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v4_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f131,f77])).

fof(f761,plain,
    ( v4_pre_topc(u1_struct_0(sK1),sK0)
    | v1_borsuk_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f171,f755])).

fof(f755,plain,(
    u1_struct_0(sK1) = u1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f753,f689])).

fof(f689,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f563,f124])).

fof(f124,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f65,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f563,plain,(
    r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f562,f81])).

fof(f81,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f562,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f388,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f388,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f387,f74])).

fof(f387,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(subsumption_resolution,[],[f386,f70])).

fof(f386,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f385,f71])).

fof(f385,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f383,f128])).

fof(f128,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f85,f83])).

fof(f83,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f85,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f383,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f280,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v3_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v3_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).

fof(f280,plain,(
    v3_pre_topc(u1_struct_0(sK1),sK1) ),
    inference(forward_demodulation,[],[f279,f127])).

fof(f127,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f126,f83])).

fof(f126,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f86,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f86,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f279,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),sK1) ),
    inference(subsumption_resolution,[],[f278,f71])).

fof(f278,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f273,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f273,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f238,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f238,plain,(
    v4_pre_topc(k1_xboole_0,sK1) ),
    inference(subsumption_resolution,[],[f236,f80])).

fof(f80,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f236,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v4_pre_topc(k1_xboole_0,sK1) ),
    inference(resolution,[],[f157,f84])).

fof(f157,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v1_xboole_0(X1)
      | v4_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f154,f70])).

fof(f154,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v4_pre_topc(X1,sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f98,f71])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f753,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f726,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f726,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f567,f124])).

fof(f567,plain,(
    r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f566,f81])).

fof(f566,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f398,f107])).

fof(f398,plain,(
    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f394,f128])).

fof(f394,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f291,f189])).

fof(f189,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f188,f70])).

fof(f188,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f187,f71])).

fof(f187,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(superposition,[],[f102,f74])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f291,plain,(
    v3_pre_topc(u1_struct_0(sK2),sK2) ),
    inference(forward_demodulation,[],[f290,f127])).

fof(f290,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) ),
    inference(subsumption_resolution,[],[f289,f73])).

fof(f73,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f289,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f285,f84])).

fof(f285,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f250,f90])).

fof(f250,plain,(
    v4_pre_topc(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f248,f80])).

fof(f248,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v4_pre_topc(k1_xboole_0,sK2) ),
    inference(resolution,[],[f158,f84])).

fof(f158,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v1_xboole_0(X2)
      | v4_pre_topc(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f155,f72])).

fof(f155,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | v4_pre_topc(X2,sK2)
      | ~ v2_pre_topc(sK2) ) ),
    inference(resolution,[],[f98,f73])).

fof(f949,plain,(
    ~ v1_borsuk_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f948,f217])).

% (8923)Termination reason: Refutation not found, incomplete strategy

% (8923)Memory used [KB]: 1918
% (8923)Time elapsed: 0.191 s
% (8923)------------------------------
% (8923)------------------------------
fof(f948,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f946,f246])).

fof(f946,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_borsuk_1(sK1,sK0) ),
    inference(resolution,[],[f886,f79])).

fof(f886,plain,(
    v1_borsuk_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f779,f883])).

fof(f779,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK1),sK0)
    | v1_borsuk_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f315,f755])).

fof(f315,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK2),sK0)
    | v1_borsuk_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f314,f68])).

fof(f314,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK2),sK0)
    | v1_borsuk_1(sK2,sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f309,f69])).

fof(f309,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK2),sK0)
    | v1_borsuk_1(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f246,f130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:51 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.21/0.47  % (8912)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.48  % (8929)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.49  % (8930)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (8906)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (8930)Refutation not found, incomplete strategy% (8930)------------------------------
% 0.21/0.51  % (8930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8930)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8930)Memory used [KB]: 6396
% 0.21/0.51  % (8930)Time elapsed: 0.105 s
% 0.21/0.51  % (8930)------------------------------
% 0.21/0.51  % (8930)------------------------------
% 0.21/0.52  % (8904)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (8909)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (8915)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (8919)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (8916)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (8905)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (8907)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (8933)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (8918)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (8933)Refutation not found, incomplete strategy% (8933)------------------------------
% 0.21/0.54  % (8933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8933)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8933)Memory used [KB]: 1791
% 0.21/0.54  % (8933)Time elapsed: 0.136 s
% 0.21/0.54  % (8933)------------------------------
% 0.21/0.54  % (8933)------------------------------
% 0.21/0.54  % (8911)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (8920)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (8920)Refutation not found, incomplete strategy% (8920)------------------------------
% 0.21/0.55  % (8920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8920)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (8920)Memory used [KB]: 10746
% 0.21/0.55  % (8920)Time elapsed: 0.137 s
% 0.21/0.55  % (8920)------------------------------
% 0.21/0.55  % (8920)------------------------------
% 0.21/0.55  % (8925)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (8910)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (8931)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (8908)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (8926)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (8928)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (8917)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (8923)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (8922)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (8913)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (8928)Refutation not found, incomplete strategy% (8928)------------------------------
% 0.21/0.56  % (8928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8928)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8928)Memory used [KB]: 10746
% 0.21/0.56  % (8928)Time elapsed: 0.161 s
% 0.21/0.56  % (8928)------------------------------
% 0.21/0.56  % (8928)------------------------------
% 1.56/0.57  % (8932)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.56/0.57  % (8921)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.56/0.57  % (8927)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.56/0.57  % (8924)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.56/0.57  % (8905)Refutation not found, incomplete strategy% (8905)------------------------------
% 1.56/0.57  % (8905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (8905)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (8905)Memory used [KB]: 1791
% 1.56/0.57  % (8905)Time elapsed: 0.163 s
% 1.56/0.57  % (8905)------------------------------
% 1.56/0.57  % (8905)------------------------------
% 1.56/0.58  % (8908)Refutation not found, incomplete strategy% (8908)------------------------------
% 1.56/0.58  % (8908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (8908)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (8908)Memory used [KB]: 1918
% 1.56/0.58  % (8908)Time elapsed: 0.180 s
% 1.56/0.58  % (8908)------------------------------
% 1.56/0.58  % (8908)------------------------------
% 1.56/0.58  % (8911)Refutation found. Thanks to Tanya!
% 1.56/0.58  % SZS status Theorem for theBenchmark
% 1.56/0.58  % (8916)Refutation not found, incomplete strategy% (8916)------------------------------
% 1.56/0.58  % (8916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % SZS output start Proof for theBenchmark
% 1.56/0.58  % (8916)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (8916)Memory used [KB]: 10874
% 1.56/0.58  % (8916)Time elapsed: 0.179 s
% 1.56/0.58  % (8916)------------------------------
% 1.56/0.58  % (8916)------------------------------
% 1.56/0.58  fof(f950,plain,(
% 1.56/0.58    $false),
% 1.56/0.58    inference(subsumption_resolution,[],[f949,f906])).
% 1.56/0.58  fof(f906,plain,(
% 1.56/0.58    v1_borsuk_1(sK1,sK0)),
% 1.56/0.58    inference(resolution,[],[f883,f244])).
% 1.56/0.58  fof(f244,plain,(
% 1.56/0.58    ~v4_pre_topc(u1_struct_0(sK1),sK0) | v1_borsuk_1(sK1,sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f243,f68])).
% 1.56/0.58  fof(f68,plain,(
% 1.56/0.58    v2_pre_topc(sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f53])).
% 1.56/0.58  fof(f53,plain,(
% 1.56/0.58    (((~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.56/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f52,f51,f50])).
% 1.56/0.58  fof(f50,plain,(
% 1.56/0.58    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_borsuk_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_borsuk_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f51,plain,(
% 1.56/0.58    ? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_borsuk_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_borsuk_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f52,plain,(
% 1.56/0.58    ? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_borsuk_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_borsuk_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,sK0) | ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_borsuk_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_borsuk_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.56/0.58    introduced(choice_axiom,[])).
% 1.56/0.58  fof(f49,plain,(
% 1.56/0.58    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.56/0.58    inference(flattening,[],[f48])).
% 1.56/0.58  fof(f48,plain,(
% 1.56/0.58    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.56/0.58    inference(nnf_transformation,[],[f27])).
% 1.56/0.58  fof(f27,plain,(
% 1.56/0.58    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.56/0.58    inference(flattening,[],[f26])).
% 1.56/0.58  fof(f26,plain,(
% 1.56/0.58    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.56/0.58    inference(ennf_transformation,[],[f23])).
% 1.56/0.58  fof(f23,negated_conjecture,(
% 1.56/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 1.56/0.58    inference(negated_conjecture,[],[f22])).
% 1.56/0.58  fof(f22,conjecture,(
% 1.56/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tmap_1)).
% 1.56/0.58  fof(f243,plain,(
% 1.56/0.58    ~v4_pre_topc(u1_struct_0(sK1),sK0) | v1_borsuk_1(sK1,sK0) | ~v2_pre_topc(sK0)),
% 1.56/0.58    inference(subsumption_resolution,[],[f239,f69])).
% 1.56/0.58  fof(f69,plain,(
% 1.56/0.58    l1_pre_topc(sK0)),
% 1.56/0.58    inference(cnf_transformation,[],[f53])).
% 1.56/0.58  fof(f239,plain,(
% 1.56/0.58    ~v4_pre_topc(u1_struct_0(sK1),sK0) | v1_borsuk_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.56/0.58    inference(resolution,[],[f217,f130])).
% 1.56/0.58  fof(f130,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | v1_borsuk_1(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.56/0.58    inference(subsumption_resolution,[],[f119,f88])).
% 1.56/0.58  fof(f88,plain,(
% 1.56/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f29])).
% 1.56/0.58  fof(f29,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.56/0.58    inference(ennf_transformation,[],[f21])).
% 1.56/0.58  fof(f21,axiom,(
% 1.56/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.56/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.56/0.58  fof(f119,plain,(
% 1.56/0.58    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.56/0.58    inference(equality_resolution,[],[f96])).
% 1.56/0.58  fof(f96,plain,(
% 1.56/0.58    ( ! [X2,X0,X1] : (v1_borsuk_1(X1,X0) | ~v4_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.56/0.58    inference(cnf_transformation,[],[f57])).
% 1.56/0.58  fof(f57,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.56/0.58    inference(flattening,[],[f56])).
% 1.56/0.58  fof(f56,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~v4_pre_topc(X2,X0)) & (v4_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.56/0.58    inference(nnf_transformation,[],[f37])).
% 1.56/0.58  fof(f37,plain,(
% 1.56/0.58    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.56/0.58    inference(flattening,[],[f36])).
% 1.56/0.58  % (8914)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.78/0.59  % (8923)Refutation not found, incomplete strategy% (8923)------------------------------
% 1.78/0.59  % (8923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  fof(f36,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.78/0.60    inference(ennf_transformation,[],[f19])).
% 1.78/0.60  fof(f19,axiom,(
% 1.78/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).
% 1.78/0.60  fof(f217,plain,(
% 1.78/0.60    m1_pre_topc(sK1,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f215,f69])).
% 1.78/0.60  fof(f215,plain,(
% 1.78/0.60    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.60    inference(duplicate_literal_removal,[],[f214])).
% 1.78/0.60  fof(f214,plain,(
% 1.78/0.60    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | m1_pre_topc(sK1,sK0)),
% 1.78/0.60    inference(resolution,[],[f180,f78])).
% 1.78/0.60  fof(f78,plain,(
% 1.78/0.60    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f180,plain,(
% 1.78/0.60    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f179,f72])).
% 1.78/0.60  fof(f72,plain,(
% 1.78/0.60    v2_pre_topc(sK2)),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f179,plain,(
% 1.78/0.60    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f178,f70])).
% 1.78/0.60  fof(f70,plain,(
% 1.78/0.60    v2_pre_topc(sK1)),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f178,plain,(
% 1.78/0.60    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~v2_pre_topc(sK1) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f177,f71])).
% 1.78/0.60  fof(f71,plain,(
% 1.78/0.60    l1_pre_topc(sK1)),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f177,plain,(
% 1.78/0.60    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(superposition,[],[f129,f74])).
% 1.78/0.60  fof(f74,plain,(
% 1.78/0.60    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f129,plain,(
% 1.78/0.60    ( ! [X2,X0] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f117,f87])).
% 1.78/0.60  fof(f87,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f28])).
% 1.78/0.60  fof(f28,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f13])).
% 1.78/0.60  fof(f13,axiom,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.78/0.60  fof(f117,plain,(
% 1.78/0.60    ( ! [X2,X0] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(equality_resolution,[],[f92])).
% 1.78/0.60  fof(f92,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f55])).
% 1.78/0.60  fof(f55,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(nnf_transformation,[],[f33])).
% 1.78/0.60  fof(f33,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(flattening,[],[f32])).
% 1.78/0.60  fof(f32,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f20])).
% 1.78/0.60  fof(f20,axiom,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).
% 1.78/0.60  fof(f883,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK1),sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f761,f302])).
% 1.78/0.60  fof(f302,plain,(
% 1.78/0.60    ~v1_borsuk_1(sK1,sK0) | v4_pre_topc(u1_struct_0(sK1),sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f301,f217])).
% 1.78/0.60  fof(f301,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f299,f246])).
% 1.78/0.60  fof(f246,plain,(
% 1.78/0.60    m1_pre_topc(sK2,sK0)),
% 1.78/0.60    inference(forward_demodulation,[],[f245,f74])).
% 1.78/0.60  fof(f245,plain,(
% 1.78/0.60    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f240,f69])).
% 1.78/0.60  fof(f240,plain,(
% 1.78/0.60    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(sK0)),
% 1.78/0.60    inference(resolution,[],[f217,f89])).
% 1.78/0.60  fof(f89,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f30])).
% 1.78/0.60  fof(f30,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f25])).
% 1.78/0.60  fof(f25,plain,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 1.78/0.60    inference(pure_predicate_removal,[],[f18])).
% 1.78/0.60  fof(f18,axiom,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 1.78/0.60  fof(f299,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(resolution,[],[f210,f79])).
% 1.78/0.60  fof(f79,plain,(
% 1.78/0.60    ~v1_borsuk_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f210,plain,(
% 1.78/0.60    v1_borsuk_1(sK2,sK0) | v4_pre_topc(u1_struct_0(sK1),sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f209,f203])).
% 1.78/0.60  fof(f203,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK2),sK0) | v4_pre_topc(u1_struct_0(sK1),sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f202,f168])).
% 1.78/0.60  fof(f168,plain,(
% 1.78/0.60    m1_pre_topc(sK1,sK0) | v4_pre_topc(u1_struct_0(sK2),sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f167,f78])).
% 1.78/0.60  fof(f167,plain,(
% 1.78/0.60    ~m1_pre_topc(sK2,sK0) | v4_pre_topc(u1_struct_0(sK2),sK0) | m1_pre_topc(sK1,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f166,f68])).
% 1.78/0.60  fof(f166,plain,(
% 1.78/0.60    ~m1_pre_topc(sK2,sK0) | v4_pre_topc(u1_struct_0(sK2),sK0) | ~v2_pre_topc(sK0) | m1_pre_topc(sK1,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f163,f69])).
% 1.78/0.60  fof(f163,plain,(
% 1.78/0.60    ~m1_pre_topc(sK2,sK0) | v4_pre_topc(u1_struct_0(sK2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_pre_topc(sK1,sK0)),
% 1.78/0.60    inference(resolution,[],[f131,f76])).
% 1.78/0.60  fof(f76,plain,(
% 1.78/0.60    v1_borsuk_1(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f131,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0) | v4_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f125,f88])).
% 1.78/0.60  fof(f125,plain,(
% 1.78/0.60    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.60    inference(duplicate_literal_removal,[],[f120])).
% 1.78/0.60  fof(f120,plain,(
% 1.78/0.60    ( ! [X0,X1] : (v4_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.60    inference(equality_resolution,[],[f95])).
% 1.78/0.60  fof(f95,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f57])).
% 1.78/0.60  fof(f202,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK2),sK0) | ~m1_pre_topc(sK1,sK0) | v4_pre_topc(u1_struct_0(sK1),sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f201,f68])).
% 1.78/0.60  fof(f201,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK2),sK0) | ~m1_pre_topc(sK1,sK0) | v4_pre_topc(u1_struct_0(sK1),sK0) | ~v2_pre_topc(sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f200,f69])).
% 1.78/0.60  fof(f200,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK2),sK0) | ~m1_pre_topc(sK1,sK0) | v4_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.78/0.60    inference(resolution,[],[f171,f131])).
% 1.78/0.60  fof(f171,plain,(
% 1.78/0.60    v1_borsuk_1(sK1,sK0) | v4_pre_topc(u1_struct_0(sK2),sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f170,f77])).
% 1.78/0.60  fof(f77,plain,(
% 1.78/0.60    v1_borsuk_1(sK1,sK0) | m1_pre_topc(sK2,sK0)),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f170,plain,(
% 1.78/0.60    ~m1_pre_topc(sK2,sK0) | v4_pre_topc(u1_struct_0(sK2),sK0) | v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f169,f68])).
% 1.78/0.60  fof(f169,plain,(
% 1.78/0.60    ~m1_pre_topc(sK2,sK0) | v4_pre_topc(u1_struct_0(sK2),sK0) | ~v2_pre_topc(sK0) | v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f164,f69])).
% 1.78/0.60  fof(f164,plain,(
% 1.78/0.60    ~m1_pre_topc(sK2,sK0) | v4_pre_topc(u1_struct_0(sK2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(resolution,[],[f131,f75])).
% 1.78/0.60  fof(f75,plain,(
% 1.78/0.60    v1_borsuk_1(sK2,sK0) | v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f209,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK1),sK0) | ~v4_pre_topc(u1_struct_0(sK2),sK0) | v1_borsuk_1(sK2,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f208,f68])).
% 1.78/0.60  fof(f208,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK1),sK0) | ~v4_pre_topc(u1_struct_0(sK2),sK0) | v1_borsuk_1(sK2,sK0) | ~v2_pre_topc(sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f204,f69])).
% 1.78/0.60  fof(f204,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK1),sK0) | ~v4_pre_topc(u1_struct_0(sK2),sK0) | v1_borsuk_1(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.78/0.60    inference(resolution,[],[f174,f130])).
% 1.78/0.60  fof(f174,plain,(
% 1.78/0.60    m1_pre_topc(sK2,sK0) | v4_pre_topc(u1_struct_0(sK1),sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f173,f78])).
% 1.78/0.60  fof(f173,plain,(
% 1.78/0.60    ~m1_pre_topc(sK1,sK0) | v4_pre_topc(u1_struct_0(sK1),sK0) | m1_pre_topc(sK2,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f172,f68])).
% 1.78/0.60  fof(f172,plain,(
% 1.78/0.60    ~m1_pre_topc(sK1,sK0) | v4_pre_topc(u1_struct_0(sK1),sK0) | ~v2_pre_topc(sK0) | m1_pre_topc(sK2,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f165,f69])).
% 1.78/0.60  fof(f165,plain,(
% 1.78/0.60    ~m1_pre_topc(sK1,sK0) | v4_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_pre_topc(sK2,sK0)),
% 1.78/0.60    inference(resolution,[],[f131,f77])).
% 1.78/0.60  fof(f761,plain,(
% 1.78/0.60    v4_pre_topc(u1_struct_0(sK1),sK0) | v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(backward_demodulation,[],[f171,f755])).
% 1.78/0.60  fof(f755,plain,(
% 1.78/0.60    u1_struct_0(sK1) = u1_struct_0(sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f753,f689])).
% 1.78/0.60  fof(f689,plain,(
% 1.78/0.60    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.78/0.60    inference(resolution,[],[f563,f124])).
% 1.78/0.60  fof(f124,plain,(
% 1.78/0.60    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.78/0.60    inference(equality_resolution,[],[f111])).
% 1.78/0.60  fof(f111,plain,(
% 1.78/0.60    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.78/0.60    inference(cnf_transformation,[],[f67])).
% 1.78/0.60  fof(f67,plain,(
% 1.78/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.78/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f65,f66])).
% 1.78/0.60  fof(f66,plain,(
% 1.78/0.60    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 1.78/0.60    introduced(choice_axiom,[])).
% 1.78/0.60  fof(f65,plain,(
% 1.78/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.78/0.60    inference(rectify,[],[f64])).
% 1.78/0.60  fof(f64,plain,(
% 1.78/0.60    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.78/0.60    inference(nnf_transformation,[],[f3])).
% 1.78/0.60  fof(f3,axiom,(
% 1.78/0.60    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.78/0.60  fof(f563,plain,(
% 1.78/0.60    r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.78/0.60    inference(subsumption_resolution,[],[f562,f81])).
% 1.78/0.60  fof(f81,plain,(
% 1.78/0.60    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f7])).
% 1.78/0.60  fof(f7,axiom,(
% 1.78/0.60    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.78/0.60  fof(f562,plain,(
% 1.78/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) | r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.78/0.60    inference(resolution,[],[f388,f107])).
% 1.78/0.60  fof(f107,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f45])).
% 1.78/0.60  fof(f45,plain,(
% 1.78/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.78/0.60    inference(flattening,[],[f44])).
% 1.78/0.60  fof(f44,plain,(
% 1.78/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.78/0.60    inference(ennf_transformation,[],[f10])).
% 1.78/0.60  fof(f10,axiom,(
% 1.78/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.78/0.60  fof(f388,plain,(
% 1.78/0.60    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.78/0.60    inference(forward_demodulation,[],[f387,f74])).
% 1.78/0.60  fof(f387,plain,(
% 1.78/0.60    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))),
% 1.78/0.60    inference(subsumption_resolution,[],[f386,f70])).
% 1.78/0.60  fof(f386,plain,(
% 1.78/0.60    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~v2_pre_topc(sK1)),
% 1.78/0.60    inference(subsumption_resolution,[],[f385,f71])).
% 1.78/0.60  fof(f385,plain,(
% 1.78/0.60    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.78/0.60    inference(subsumption_resolution,[],[f383,f128])).
% 1.78/0.60  fof(f128,plain,(
% 1.78/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.78/0.60    inference(forward_demodulation,[],[f85,f83])).
% 1.78/0.60  fof(f83,plain,(
% 1.78/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.78/0.60    inference(cnf_transformation,[],[f5])).
% 1.78/0.60  fof(f5,axiom,(
% 1.78/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.78/0.60  fof(f85,plain,(
% 1.78/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f6])).
% 1.78/0.60  fof(f6,axiom,(
% 1.78/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.78/0.60  fof(f383,plain,(
% 1.78/0.60    ~m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 1.78/0.60    inference(resolution,[],[f280,f100])).
% 1.78/0.60  fof(f100,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f59])).
% 1.78/0.60  fof(f59,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.78/0.60    inference(flattening,[],[f58])).
% 1.78/0.60  fof(f58,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.78/0.60    inference(nnf_transformation,[],[f41])).
% 1.78/0.60  fof(f41,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.78/0.60    inference(flattening,[],[f40])).
% 1.78/0.60  fof(f40,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.78/0.60    inference(ennf_transformation,[],[f15])).
% 1.78/0.60  fof(f15,axiom,(
% 1.78/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_pre_topc)).
% 1.78/0.60  fof(f280,plain,(
% 1.78/0.60    v3_pre_topc(u1_struct_0(sK1),sK1)),
% 1.78/0.60    inference(forward_demodulation,[],[f279,f127])).
% 1.78/0.60  fof(f127,plain,(
% 1.78/0.60    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.78/0.60    inference(backward_demodulation,[],[f126,f83])).
% 1.78/0.60  fof(f126,plain,(
% 1.78/0.60    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.78/0.60    inference(forward_demodulation,[],[f86,f82])).
% 1.78/0.60  fof(f82,plain,(
% 1.78/0.60    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f4])).
% 1.78/0.60  fof(f4,axiom,(
% 1.78/0.60    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.78/0.60  fof(f86,plain,(
% 1.78/0.60    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f8])).
% 1.78/0.60  fof(f8,axiom,(
% 1.78/0.60    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.78/0.60  fof(f279,plain,(
% 1.78/0.60    v3_pre_topc(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),sK1)),
% 1.78/0.60    inference(subsumption_resolution,[],[f278,f71])).
% 1.78/0.60  fof(f278,plain,(
% 1.78/0.60    v3_pre_topc(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),sK1) | ~l1_pre_topc(sK1)),
% 1.78/0.60    inference(subsumption_resolution,[],[f273,f84])).
% 1.78/0.60  fof(f84,plain,(
% 1.78/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.78/0.60    inference(cnf_transformation,[],[f9])).
% 1.78/0.60  fof(f9,axiom,(
% 1.78/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.78/0.60  fof(f273,plain,(
% 1.78/0.60    v3_pre_topc(k3_subset_1(u1_struct_0(sK1),k1_xboole_0),sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.78/0.60    inference(resolution,[],[f238,f90])).
% 1.78/0.60  fof(f90,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f54])).
% 1.78/0.60  fof(f54,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(nnf_transformation,[],[f31])).
% 1.78/0.60  fof(f31,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f17])).
% 1.78/0.60  fof(f17,axiom,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 1.78/0.60  fof(f238,plain,(
% 1.78/0.60    v4_pre_topc(k1_xboole_0,sK1)),
% 1.78/0.60    inference(subsumption_resolution,[],[f236,f80])).
% 1.78/0.60  fof(f80,plain,(
% 1.78/0.60    v1_xboole_0(k1_xboole_0)),
% 1.78/0.60    inference(cnf_transformation,[],[f1])).
% 1.78/0.60  fof(f1,axiom,(
% 1.78/0.60    v1_xboole_0(k1_xboole_0)),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.78/0.60  fof(f236,plain,(
% 1.78/0.60    ~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,sK1)),
% 1.78/0.60    inference(resolution,[],[f157,f84])).
% 1.78/0.60  fof(f157,plain,(
% 1.78/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,sK1)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f154,f70])).
% 1.78/0.60  fof(f154,plain,(
% 1.78/0.60    ( ! [X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(X1,sK1) | ~v2_pre_topc(sK1)) )),
% 1.78/0.60    inference(resolution,[],[f98,f71])).
% 1.78/0.60  fof(f98,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f39])).
% 1.78/0.60  fof(f39,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.78/0.60    inference(flattening,[],[f38])).
% 1.78/0.60  fof(f38,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.78/0.60    inference(ennf_transformation,[],[f12])).
% 1.78/0.60  fof(f12,axiom,(
% 1.78/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).
% 1.78/0.60  fof(f753,plain,(
% 1.78/0.60    u1_struct_0(sK1) = u1_struct_0(sK2) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))),
% 1.78/0.60    inference(resolution,[],[f726,f110])).
% 1.78/0.60  fof(f110,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f63])).
% 1.78/0.60  fof(f63,plain,(
% 1.78/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.78/0.60    inference(flattening,[],[f62])).
% 1.78/0.60  fof(f62,plain,(
% 1.78/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.78/0.60    inference(nnf_transformation,[],[f2])).
% 1.78/0.60  fof(f2,axiom,(
% 1.78/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.78/0.60  fof(f726,plain,(
% 1.78/0.60    r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))),
% 1.78/0.60    inference(resolution,[],[f567,f124])).
% 1.78/0.60  fof(f567,plain,(
% 1.78/0.60    r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.78/0.60    inference(subsumption_resolution,[],[f566,f81])).
% 1.78/0.60  fof(f566,plain,(
% 1.78/0.60    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) | r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.78/0.60    inference(resolution,[],[f398,f107])).
% 1.78/0.60  fof(f398,plain,(
% 1.78/0.60    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.78/0.60    inference(subsumption_resolution,[],[f394,f128])).
% 1.78/0.60  fof(f394,plain,(
% 1.78/0.60    ~m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.78/0.60    inference(resolution,[],[f291,f189])).
% 1.78/0.60  fof(f189,plain,(
% 1.78/0.60    ( ! [X0] : (~v3_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f188,f70])).
% 1.78/0.60  fof(f188,plain,(
% 1.78/0.60    ( ! [X0] : (~v3_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v2_pre_topc(sK1)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f187,f71])).
% 1.78/0.60  fof(f187,plain,(
% 1.78/0.60    ( ! [X0] : (~v3_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 1.78/0.60    inference(superposition,[],[f102,f74])).
% 1.78/0.60  fof(f102,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f59])).
% 1.78/0.60  fof(f291,plain,(
% 1.78/0.60    v3_pre_topc(u1_struct_0(sK2),sK2)),
% 1.78/0.60    inference(forward_demodulation,[],[f290,f127])).
% 1.78/0.60  fof(f290,plain,(
% 1.78/0.60    v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f289,f73])).
% 1.78/0.60  fof(f73,plain,(
% 1.78/0.60    l1_pre_topc(sK2)),
% 1.78/0.60    inference(cnf_transformation,[],[f53])).
% 1.78/0.60  fof(f289,plain,(
% 1.78/0.60    v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) | ~l1_pre_topc(sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f285,f84])).
% 1.78/0.60  fof(f285,plain,(
% 1.78/0.60    v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k1_xboole_0),sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)),
% 1.78/0.60    inference(resolution,[],[f250,f90])).
% 1.78/0.60  fof(f250,plain,(
% 1.78/0.60    v4_pre_topc(k1_xboole_0,sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f248,f80])).
% 1.78/0.60  fof(f248,plain,(
% 1.78/0.60    ~v1_xboole_0(k1_xboole_0) | v4_pre_topc(k1_xboole_0,sK2)),
% 1.78/0.60    inference(resolution,[],[f158,f84])).
% 1.78/0.60  fof(f158,plain,(
% 1.78/0.60    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | ~v1_xboole_0(X2) | v4_pre_topc(X2,sK2)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f155,f72])).
% 1.78/0.60  fof(f155,plain,(
% 1.78/0.60    ( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(X2,sK2) | ~v2_pre_topc(sK2)) )),
% 1.78/0.60    inference(resolution,[],[f98,f73])).
% 1.78/0.60  fof(f949,plain,(
% 1.78/0.60    ~v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f948,f217])).
% 1.78/0.60  % (8923)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (8923)Memory used [KB]: 1918
% 1.78/0.60  % (8923)Time elapsed: 0.191 s
% 1.78/0.60  % (8923)------------------------------
% 1.78/0.60  % (8923)------------------------------
% 1.78/0.60  fof(f948,plain,(
% 1.78/0.60    ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f946,f246])).
% 1.78/0.60  fof(f946,plain,(
% 1.78/0.60    ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_borsuk_1(sK1,sK0)),
% 1.78/0.60    inference(resolution,[],[f886,f79])).
% 1.78/0.60  fof(f886,plain,(
% 1.78/0.60    v1_borsuk_1(sK2,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f779,f883])).
% 1.78/0.60  fof(f779,plain,(
% 1.78/0.60    ~v4_pre_topc(u1_struct_0(sK1),sK0) | v1_borsuk_1(sK2,sK0)),
% 1.78/0.60    inference(backward_demodulation,[],[f315,f755])).
% 1.78/0.60  fof(f315,plain,(
% 1.78/0.60    ~v4_pre_topc(u1_struct_0(sK2),sK0) | v1_borsuk_1(sK2,sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f314,f68])).
% 1.78/0.60  fof(f314,plain,(
% 1.78/0.60    ~v4_pre_topc(u1_struct_0(sK2),sK0) | v1_borsuk_1(sK2,sK0) | ~v2_pre_topc(sK0)),
% 1.78/0.60    inference(subsumption_resolution,[],[f309,f69])).
% 1.78/0.60  fof(f309,plain,(
% 1.78/0.60    ~v4_pre_topc(u1_struct_0(sK2),sK0) | v1_borsuk_1(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.78/0.60    inference(resolution,[],[f246,f130])).
% 1.78/0.60  % SZS output end Proof for theBenchmark
% 1.78/0.60  % (8911)------------------------------
% 1.78/0.60  % (8911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (8911)Termination reason: Refutation
% 1.78/0.60  
% 1.78/0.60  % (8911)Memory used [KB]: 2174
% 1.78/0.60  % (8911)Time elapsed: 0.182 s
% 1.78/0.60  % (8911)------------------------------
% 1.78/0.60  % (8911)------------------------------
% 1.78/0.60  % (8903)Success in time 0.236 s
%------------------------------------------------------------------------------
