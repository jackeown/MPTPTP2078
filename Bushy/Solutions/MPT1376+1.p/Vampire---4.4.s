%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t32_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:51 EDT 2019

% Result     : Theorem 2.35s
% Output     : Refutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 541 expanded)
%              Number of leaves         :   32 ( 162 expanded)
%              Depth                    :   18
%              Number of atoms          :  734 (3267 expanded)
%              Number of equality atoms :   24 ( 107 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16794,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f160,f163,f355,f1466,f11062,f11110,f11268,f11354,f11356,f11364,f14913,f14926,f14950,f16788,f16792])).

fof(f16792,plain,
    ( ~ spl9_2
    | spl9_5
    | ~ spl9_26
    | ~ spl9_1104
    | spl9_1453 ),
    inference(avatar_contradiction_clause,[],[f16791])).

fof(f16791,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1453 ),
    inference(subsumption_resolution,[],[f16790,f14954])).

fof(f14954,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_1104 ),
    inference(subsumption_resolution,[],[f14953,f143])).

fof(f143,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f14953,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_1104 ),
    inference(forward_demodulation,[],[f14952,f11160])).

fof(f11160,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_1104 ),
    inference(equality_resolution,[],[f11061])).

fof(f11061,plain,
    ( ! [X2,X1] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 )
    | ~ spl9_1104 ),
    inference(avatar_component_clause,[],[f11060])).

fof(f11060,plain,
    ( spl9_1104
  <=> ! [X1,X2] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1104])])).

fof(f14952,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_1104 ),
    inference(forward_demodulation,[],[f14951,f11160])).

fof(f14951,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f14930,f327])).

fof(f327,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl9_26
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f14930,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_5 ),
    inference(resolution,[],[f152,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK2(X0,X1),X0)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f66,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t32_compts_1.p',d1_tops_2)).

fof(f152,plain,
    ( ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl9_5
  <=> ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f16790,plain,
    ( ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1453 ),
    inference(forward_demodulation,[],[f16789,f11160])).

fof(f16789,plain,
    ( ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1453 ),
    inference(forward_demodulation,[],[f14949,f11217])).

fof(f11217,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl9_26
    | ~ spl9_1104 ),
    inference(backward_demodulation,[],[f11160,f4547])).

fof(f4547,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f4546,f85])).

fof(f85,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
      | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        & v1_tops_2(sK1,sK0) ) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f61,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              | ~ v1_tops_2(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
                & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                & v1_tops_2(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
            | ~ v1_tops_2(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
              & v1_tops_2(X1,sK0) ) ) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) ) ) )
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
          | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
          | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
          | ~ v1_tops_2(sK1,X0) )
        & ( ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(sK1,X0) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t32_compts_1.p',t32_compts_1)).

fof(f4546,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ v2_pre_topc(sK0)
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f4540,f86])).

fof(f86,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f4540,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_26 ),
    inference(resolution,[],[f276,f327])).

fof(f276,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2) ) ),
    inference(resolution,[],[f96,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t32_compts_1.p',fc6_pre_topc)).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t32_compts_1.p',abstractness_v1_pre_topc)).

fof(f14949,plain,
    ( ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ spl9_1453 ),
    inference(avatar_component_clause,[],[f14948])).

fof(f14948,plain,
    ( spl9_1453
  <=> ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1453])])).

fof(f16788,plain,
    ( ~ spl9_0
    | ~ spl9_2
    | spl9_5
    | ~ spl9_26
    | ~ spl9_1104
    | spl9_1451 ),
    inference(avatar_contradiction_clause,[],[f16787])).

fof(f16787,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1451 ),
    inference(subsumption_resolution,[],[f16786,f143])).

fof(f16786,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1451 ),
    inference(subsumption_resolution,[],[f16785,f137])).

fof(f137,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl9_0
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f16785,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1451 ),
    inference(resolution,[],[f16536,f14957])).

fof(f14957,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_1104 ),
    inference(subsumption_resolution,[],[f14956,f143])).

fof(f14956,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_1104 ),
    inference(forward_demodulation,[],[f14955,f11160])).

fof(f14955,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f14931,f327])).

fof(f14931,plain,
    ( r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_5 ),
    inference(resolution,[],[f152,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f16536,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1451 ),
    inference(resolution,[],[f16139,f3850])).

fof(f3850,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ v1_tops_2(X0,sK0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f3846,f86])).

fof(f3846,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ l1_pre_topc(sK0)
      | v3_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f1393,f85])).

fof(f1393,plain,(
    ! [X6,X8,X7] :
      ( ~ v2_pre_topc(X8)
      | ~ v1_tops_2(X7,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
      | ~ l1_pre_topc(X8)
      | v3_pre_topc(X6,g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)))
      | ~ r2_hidden(X6,X7) ) ),
    inference(subsumption_resolution,[],[f1389,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t32_compts_1.p',t4_subset)).

fof(f1389,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ v1_tops_2(X7,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
      | ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X8)))
      | v3_pre_topc(X6,g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)))
      | ~ v2_pre_topc(X8) ) ),
    inference(duplicate_literal_removal,[],[f1388])).

fof(f1388,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ v1_tops_2(X7,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X8))))
      | ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X8)))
      | v3_pre_topc(X6,g1_pre_topc(u1_struct_0(X8),u1_pre_topc(X8)))
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8) ) ),
    inference(resolution,[],[f1296,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
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
    inference(flattening,[],[f71])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v3_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t32_compts_1.p',t60_pre_topc)).

fof(f1296,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f97,f126])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f16139,plain,
    ( ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1451 ),
    inference(forward_demodulation,[],[f14943,f11217])).

fof(f14943,plain,
    ( ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl9_1451 ),
    inference(avatar_component_clause,[],[f14942])).

fof(f14942,plain,
    ( spl9_1451
  <=> ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1451])])).

fof(f14950,plain,
    ( ~ spl9_1451
    | ~ spl9_1453
    | ~ spl9_2
    | spl9_5
    | ~ spl9_26
    | ~ spl9_30
    | ~ spl9_1104 ),
    inference(avatar_split_clause,[],[f14937,f11060,f339,f326,f151,f142,f14948,f14942])).

fof(f339,plain,
    ( spl9_30
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f14937,plain,
    ( ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl9_2
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_30
    | ~ spl9_1104 ),
    inference(subsumption_resolution,[],[f14936,f143])).

fof(f14936,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_30
    | ~ spl9_1104 ),
    inference(forward_demodulation,[],[f14935,f11160])).

fof(f14935,plain,
    ( ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_30
    | ~ spl9_1104 ),
    inference(forward_demodulation,[],[f14934,f11160])).

fof(f14934,plain,
    ( ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_30
    | ~ spl9_1104 ),
    inference(forward_demodulation,[],[f14933,f11160])).

fof(f14933,plain,
    ( ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_5
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f14932,f340])).

fof(f340,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f339])).

fof(f14932,plain,
    ( ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_5
    | ~ spl9_26 ),
    inference(subsumption_resolution,[],[f14929,f327])).

fof(f14929,plain,
    ( ~ v3_pre_topc(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_5 ),
    inference(resolution,[],[f152,f1483])).

fof(f1483,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK2(X0,X1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(duplicate_literal_removal,[],[f1478])).

fof(f1478,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(sK2(X0,X1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f109,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK2(X0,X1),X0)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f14926,plain,
    ( ~ spl9_2
    | spl9_7
    | ~ spl9_1104 ),
    inference(avatar_contradiction_clause,[],[f14925])).

fof(f14925,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_1104 ),
    inference(subsumption_resolution,[],[f14924,f143])).

fof(f14924,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_7
    | ~ spl9_1104 ),
    inference(forward_demodulation,[],[f158,f11160])).

fof(f158,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl9_7
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f14913,plain,
    ( ~ spl9_2
    | ~ spl9_4
    | ~ spl9_26
    | ~ spl9_1104
    | spl9_1137
    | ~ spl9_1140 ),
    inference(avatar_contradiction_clause,[],[f14912])).

fof(f14912,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1137
    | ~ spl9_1140 ),
    inference(subsumption_resolution,[],[f14911,f149])).

fof(f149,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl9_4
  <=> v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f14911,plain,
    ( ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_2
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1137
    | ~ spl9_1140 ),
    inference(subsumption_resolution,[],[f14909,f143])).

fof(f14909,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1137
    | ~ spl9_1140 ),
    inference(resolution,[],[f14683,f11363])).

fof(f11363,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl9_1140 ),
    inference(avatar_component_clause,[],[f11362])).

fof(f11362,plain,
    ( spl9_1140
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1140])])).

fof(f14683,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,sK1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl9_26
    | ~ spl9_1104
    | ~ spl9_1137 ),
    inference(forward_demodulation,[],[f14682,f11160])).

fof(f14682,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,sK1),X1)
        | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) )
    | ~ spl9_26
    | ~ spl9_1137 ),
    inference(subsumption_resolution,[],[f14664,f327])).

fof(f14664,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK2(sK0,sK1),X1)
        | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl9_1137 ),
    inference(resolution,[],[f11347,f1296])).

fof(f11347,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_1137 ),
    inference(avatar_component_clause,[],[f11346])).

fof(f11346,plain,
    ( spl9_1137
  <=> ~ v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1137])])).

fof(f11364,plain,
    ( ~ spl9_3
    | spl9_1140
    | spl9_1 ),
    inference(avatar_split_clause,[],[f11357,f139,f11362,f145])).

fof(f145,plain,
    ( spl9_3
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f139,plain,
    ( spl9_1
  <=> ~ v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f11357,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f11338,f86])).

fof(f11338,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1 ),
    inference(resolution,[],[f140,f99])).

fof(f140,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f11356,plain,
    ( ~ spl9_3
    | spl9_1138
    | spl9_1 ),
    inference(avatar_split_clause,[],[f11355,f139,f11349,f145])).

fof(f11349,plain,
    ( spl9_1138
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1138])])).

fof(f11355,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f11337,f86])).

fof(f11337,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_1 ),
    inference(resolution,[],[f140,f98])).

fof(f11354,plain,
    ( ~ spl9_3
    | ~ spl9_1137
    | ~ spl9_1139
    | spl9_1
    | ~ spl9_1104 ),
    inference(avatar_split_clause,[],[f11341,f11060,f139,f11352,f11346,f145])).

fof(f11352,plain,
    ( spl9_1139
  <=> ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1139])])).

fof(f11341,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_1
    | ~ spl9_1104 ),
    inference(forward_demodulation,[],[f11340,f11160])).

fof(f11340,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f11339,f85])).

fof(f11339,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f11336,f86])).

fof(f11336,plain,
    ( ~ v3_pre_topc(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_1 ),
    inference(resolution,[],[f140,f1483])).

fof(f11268,plain,
    ( spl9_3
    | ~ spl9_6
    | ~ spl9_1104 ),
    inference(avatar_contradiction_clause,[],[f11267])).

fof(f11267,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_6
    | ~ spl9_1104 ),
    inference(subsumption_resolution,[],[f11161,f146])).

fof(f146,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f11161,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_6
    | ~ spl9_1104 ),
    inference(backward_demodulation,[],[f11160,f155])).

fof(f155,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl9_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f11110,plain,
    ( ~ spl9_26
    | spl9_1101 ),
    inference(avatar_contradiction_clause,[],[f11109])).

fof(f11109,plain,
    ( $false
    | ~ spl9_26
    | ~ spl9_1101 ),
    inference(subsumption_resolution,[],[f11108,f327])).

fof(f11108,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_1101 ),
    inference(resolution,[],[f11051,f95])).

fof(f95,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t32_compts_1.p',dt_u1_pre_topc)).

fof(f11051,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl9_1101 ),
    inference(avatar_component_clause,[],[f11050])).

fof(f11050,plain,
    ( spl9_1101
  <=> ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1101])])).

fof(f11062,plain,
    ( ~ spl9_1101
    | spl9_1104
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f11017,f326,f11060,f11050])).

fof(f11017,plain,
    ( ! [X2,X1] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) )
    | ~ spl9_26 ),
    inference(superposition,[],[f120,f4547])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t32_compts_1.p',free_g1_pre_topc)).

fof(f1466,plain,(
    spl9_31 ),
    inference(avatar_contradiction_clause,[],[f1465])).

fof(f1465,plain,
    ( $false
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1464,f85])).

fof(f1464,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl9_31 ),
    inference(subsumption_resolution,[],[f1463,f86])).

fof(f1463,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl9_31 ),
    inference(resolution,[],[f343,f106])).

fof(f106,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f343,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl9_31
  <=> ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f355,plain,(
    spl9_27 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f353,f86])).

fof(f353,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl9_27 ),
    inference(resolution,[],[f352,f95])).

fof(f352,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_27 ),
    inference(resolution,[],[f330,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/compts_1__t32_compts_1.p',dt_g1_pre_topc)).

fof(f330,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl9_27
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f163,plain,
    ( spl9_0
    | spl9_4 ),
    inference(avatar_split_clause,[],[f87,f148,f136])).

fof(f87,plain,
    ( v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f160,plain,
    ( spl9_2
    | spl9_6 ),
    inference(avatar_split_clause,[],[f90,f154,f142])).

fof(f90,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f64])).

fof(f159,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | ~ spl9_5
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f91,f157,f151,f145,f139])).

fof(f91,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v1_tops_2(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
