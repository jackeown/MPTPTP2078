%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t33_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:51 EDT 2019

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  292 (1155 expanded)
%              Number of leaves         :   41 ( 363 expanded)
%              Depth                    :   38
%              Number of atoms          : 1902 (8806 expanded)
%              Number of equality atoms :   41 ( 206 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21631,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f165,f166,f169,f312,f940,f944,f967,f1746,f1798,f3973,f6851,f11859,f11912,f11933,f11965,f14028,f14030,f14041,f15315,f15323,f15542,f15550,f21574,f21630])).

fof(f21630,plain,
    ( spl10_3
    | ~ spl10_6
    | ~ spl10_218 ),
    inference(avatar_contradiction_clause,[],[f21629])).

fof(f21629,plain,
    ( $false
    | ~ spl10_3
    | ~ spl10_6
    | ~ spl10_218 ),
    inference(subsumption_resolution,[],[f1829,f152])).

fof(f152,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl10_3
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f1829,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_6
    | ~ spl10_218 ),
    inference(backward_demodulation,[],[f1828,f161])).

fof(f161,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f1828,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_218 ),
    inference(equality_resolution,[],[f1745])).

fof(f1745,plain,
    ( ! [X2,X1] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 )
    | ~ spl10_218 ),
    inference(avatar_component_clause,[],[f1744])).

fof(f1744,plain,
    ( spl10_218
  <=> ! [X1,X2] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_218])])).

fof(f21574,plain,
    ( ~ spl10_3
    | ~ spl10_1
    | ~ spl10_218
    | ~ spl10_436
    | ~ spl10_1744
    | ~ spl10_1746
    | ~ spl10_1760 ),
    inference(avatar_split_clause,[],[f21573,f15540,f15313,f15304,f3932,f1744,f145,f151])).

fof(f145,plain,
    ( spl10_1
  <=> ~ v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f3932,plain,
    ( spl10_436
  <=> m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_436])])).

fof(f15304,plain,
    ( spl10_1744
  <=> v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1744])])).

fof(f15313,plain,
    ( spl10_1746
  <=> m1_subset_1(sK3(sK0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1746])])).

fof(f15540,plain,
    ( spl10_1760
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1760])])).

fof(f21573,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_218
    | ~ spl10_436
    | ~ spl10_1744
    | ~ spl10_1746
    | ~ spl10_1760 ),
    inference(subsumption_resolution,[],[f21572,f3992])).

fof(f3992,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_218
    | ~ spl10_436 ),
    inference(forward_demodulation,[],[f3933,f1828])).

fof(f3933,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl10_436 ),
    inference(avatar_component_clause,[],[f3932])).

fof(f21572,plain,
    ( ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_218
    | ~ spl10_1744
    | ~ spl10_1746
    | ~ spl10_1760 ),
    inference(forward_demodulation,[],[f21571,f1828])).

fof(f21571,plain,
    ( ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1744
    | ~ spl10_1746
    | ~ spl10_1760 ),
    inference(subsumption_resolution,[],[f21564,f89])).

fof(f89,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f63,f65,f64])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v2_compts_1(X1,X0) )
            & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
                & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
              | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v2_compts_1(X1,X0) ) ) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_compts_1(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_compts_1(X1,sK0) ) ) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
          | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
          | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v2_compts_1(sK1,X0) )
        & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(sK1,X0) ) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v2_compts_1(X1,X0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) ) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
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
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',t33_compts_1)).

fof(f21564,plain,
    ( ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1744
    | ~ spl10_1746
    | ~ spl10_1760 ),
    inference(subsumption_resolution,[],[f21563,f15305])).

fof(f15305,plain,
    ( v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1744 ),
    inference(avatar_component_clause,[],[f15304])).

fof(f21563,plain,
    ( ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1746
    | ~ spl10_1760 ),
    inference(subsumption_resolution,[],[f21562,f88])).

fof(f88,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f21562,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1746
    | ~ spl10_1760 ),
    inference(subsumption_resolution,[],[f21559,f87])).

fof(f87,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f21559,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1746
    | ~ spl10_1760 ),
    inference(resolution,[],[f15541,f15314])).

fof(f15314,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_1746 ),
    inference(avatar_component_clause,[],[f15313])).

fof(f15541,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl10_1760 ),
    inference(avatar_component_clause,[],[f15540])).

fof(f15550,plain,
    ( ~ spl10_2
    | spl10_5
    | ~ spl10_22
    | ~ spl10_218
    | spl10_1759 ),
    inference(avatar_contradiction_clause,[],[f15549])).

fof(f15549,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_1759 ),
    inference(subsumption_resolution,[],[f15548,f149])).

fof(f149,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl10_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f15548,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_1759 ),
    inference(forward_demodulation,[],[f15547,f1828])).

fof(f15547,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_1759 ),
    inference(subsumption_resolution,[],[f15546,f283])).

fof(f283,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl10_22
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f15546,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_5
    | ~ spl10_1759 ),
    inference(subsumption_resolution,[],[f15545,f158])).

fof(f158,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl10_5
  <=> ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f15545,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1759 ),
    inference(resolution,[],[f15538,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(sK2(X0,X1),X1)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ( ! [X3] :
                    ( ~ v1_finset_1(X3)
                    | ~ m1_setfam_1(X3,X1)
                    | ~ r1_tarski(X3,sK2(X0,X1))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                & v1_tops_2(sK2(X0,X1),X0)
                & m1_setfam_1(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ( v1_finset_1(sK3(X0,X1,X4))
                    & m1_setfam_1(sK3(X0,X1,X4),X1)
                    & r1_tarski(sK3(X0,X1,X4),X4)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f68,f70,f69])).

fof(f69,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ v1_finset_1(X3)
              | ~ m1_setfam_1(X3,X1)
              | ~ r1_tarski(X3,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & v1_tops_2(X2,X0)
          & m1_setfam_1(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ! [X3] :
            ( ~ v1_finset_1(X3)
            | ~ m1_setfam_1(X3,X1)
            | ~ r1_tarski(X3,sK2(X0,X1))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & v1_tops_2(sK2(X0,X1),X0)
        & m1_setfam_1(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( v1_finset_1(X5)
          & m1_setfam_1(X5,X1)
          & r1_tarski(X5,X4)
          & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( v1_finset_1(sK3(X0,X1,X4))
        & m1_setfam_1(sK3(X0,X1,X4),X1)
        & r1_tarski(sK3(X0,X1,X4),X4)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( v1_finset_1(X5)
                      & m1_setfam_1(X5,X1)
                      & r1_tarski(X5,X4)
                      & m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X4,X0)
                  | ~ m1_setfam_1(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_compts_1(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( ~ v1_finset_1(X3)
                      | ~ m1_setfam_1(X3,X1)
                      | ~ r1_tarski(X3,X2)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  & v1_tops_2(X2,X0)
                  & m1_setfam_1(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( v1_finset_1(X3)
                      & m1_setfam_1(X3,X1)
                      & r1_tarski(X3,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                  | ~ v1_tops_2(X2,X0)
                  | ~ m1_setfam_1(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
              | ~ v2_compts_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( v1_finset_1(X3)
                    & m1_setfam_1(X3,X1)
                    & r1_tarski(X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
                | ~ v1_tops_2(X2,X0)
                | ~ m1_setfam_1(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_compts_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
                       => ~ ( v1_finset_1(X3)
                            & m1_setfam_1(X3,X1)
                            & r1_tarski(X3,X2) ) )
                    & v1_tops_2(X2,X0)
                    & m1_setfam_1(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',d7_compts_1)).

fof(f15538,plain,
    ( ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
    | ~ spl10_1759 ),
    inference(avatar_component_clause,[],[f15537])).

fof(f15537,plain,
    ( spl10_1759
  <=> ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1759])])).

fof(f15542,plain,
    ( ~ spl10_1759
    | spl10_1760
    | ~ spl10_2
    | spl10_5
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_432 ),
    inference(avatar_split_clause,[],[f15532,f3914,f1744,f282,f157,f148,f15540,f15537])).

fof(f3914,plain,
    ( spl10_432
  <=> ! [X0] :
        ( r1_tarski(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_432])])).

fof(f15532,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) )
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f15531,f149])).

fof(f15531,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1) )
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_432 ),
    inference(forward_demodulation,[],[f15530,f1828])).

fof(f15530,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_432 ),
    inference(forward_demodulation,[],[f15529,f1828])).

fof(f15529,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
        | ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f15528,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',t32_compts_1)).

fof(f15528,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f15527,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f15527,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f15526,f102])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( m1_setfam_1(sK3(X0,X1,X4),X1)
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f15526,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_setfam_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),sK1)
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) )
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f15525,f283])).

fof(f15525,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_setfam_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),sK1)
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl10_5
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f15524,f158])).

fof(f15524,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_setfam_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),sK1)
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl10_432 ),
    inference(duplicate_literal_removal,[],[f15520])).

fof(f15520,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_setfam_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK1)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_setfam_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),sK1)
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ m1_subset_1(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl10_432 ),
    inference(resolution,[],[f14765,f875])).

fof(f875,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(sK3(X1,X2,X0),sK2(X4,X3))
      | ~ m1_setfam_1(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
      | ~ v2_compts_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | v2_compts_1(X3,X4)
      | ~ m1_setfam_1(sK3(X1,X2,X0),X3)
      | ~ v1_tops_2(X0,X1)
      | ~ m1_subset_1(sK3(X1,X2,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f103,f107])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_finset_1(X3)
      | v2_compts_1(X1,X0)
      | ~ m1_setfam_1(X3,X1)
      | ~ r1_tarski(X3,sK2(X0,X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f103,plain,(
    ! [X4,X0,X1] :
      ( v1_finset_1(sK3(X0,X1,X4))
      | ~ v1_tops_2(X4,X0)
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f14765,plain,
    ( ! [X1] :
        ( r1_tarski(sK3(X1,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v2_compts_1(sK1,X1)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_432 ),
    inference(subsumption_resolution,[],[f14762,f111])).

fof(f14762,plain,
    ( ! [X1] :
        ( r1_tarski(sK3(X1,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v2_compts_1(sK1,X1)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_432 ),
    inference(duplicate_literal_removal,[],[f14761])).

fof(f14761,plain,
    ( ! [X1] :
        ( r1_tarski(sK3(X1,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v2_compts_1(sK1,X1)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl10_432 ),
    inference(resolution,[],[f3915,f110])).

fof(f3915,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | r1_tarski(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
    | ~ spl10_432 ),
    inference(avatar_component_clause,[],[f3914])).

fof(f15323,plain,
    ( ~ spl10_2
    | spl10_5
    | ~ spl10_22
    | ~ spl10_218
    | spl10_1745 ),
    inference(avatar_contradiction_clause,[],[f15322])).

fof(f15322,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_1745 ),
    inference(subsumption_resolution,[],[f15321,f149])).

fof(f15321,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_1745 ),
    inference(forward_demodulation,[],[f15320,f1828])).

fof(f15320,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl10_5
    | ~ spl10_22
    | ~ spl10_1745 ),
    inference(subsumption_resolution,[],[f15319,f283])).

fof(f15319,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_5
    | ~ spl10_1745 ),
    inference(subsumption_resolution,[],[f15316,f158])).

fof(f15316,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1745 ),
    inference(resolution,[],[f15308,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_tops_2(sK2(X0,X1),X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f15308,plain,
    ( ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1745 ),
    inference(avatar_component_clause,[],[f15307])).

fof(f15307,plain,
    ( spl10_1745
  <=> ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1745])])).

fof(f15315,plain,
    ( ~ spl10_1745
    | spl10_1746
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_218
    | ~ spl10_436
    | ~ spl10_1672 ),
    inference(avatar_split_clause,[],[f15302,f14039,f3932,f1744,f148,f142,f15313,f15307])).

fof(f142,plain,
    ( spl10_0
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f14039,plain,
    ( spl10_1672
  <=> ! [X1] :
        ( ~ v2_compts_1(sK1,X1)
        | m1_subset_1(sK3(X1,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1672])])).

fof(f15302,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_218
    | ~ spl10_436
    | ~ spl10_1672 ),
    inference(subsumption_resolution,[],[f15301,f3992])).

fof(f15301,plain,
    ( ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | m1_subset_1(sK3(sK0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_218
    | ~ spl10_1672 ),
    inference(forward_demodulation,[],[f15300,f1828])).

fof(f15300,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_1672 ),
    inference(subsumption_resolution,[],[f15299,f149])).

fof(f15299,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_0
    | ~ spl10_1672 ),
    inference(subsumption_resolution,[],[f15298,f89])).

fof(f15298,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_0
    | ~ spl10_1672 ),
    inference(subsumption_resolution,[],[f15297,f143])).

fof(f143,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f142])).

fof(f15297,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_compts_1(sK1,sK0)
    | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1672 ),
    inference(subsumption_resolution,[],[f15293,f87])).

fof(f15293,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_struct_0(sK0)
    | ~ v2_compts_1(sK1,sK0)
    | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1672 ),
    inference(resolution,[],[f14040,f88])).

fof(f14040,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(X1)
        | m1_subset_1(sK3(X1,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | v2_struct_0(X1)
        | ~ v2_compts_1(sK1,X1)
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) )
    | ~ spl10_1672 ),
    inference(avatar_component_clause,[],[f14039])).

fof(f14041,plain,
    ( ~ spl10_23
    | ~ spl10_7
    | spl10_1672
    | spl10_5 ),
    inference(avatar_split_clause,[],[f14024,f157,f14039,f163,f285])).

fof(f285,plain,
    ( spl10_23
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f163,plain,
    ( spl10_7
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f14024,plain,
    ( ! [X1] :
        ( ~ v2_compts_1(sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1)
        | m1_subset_1(sK3(X1,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl10_5 ),
    inference(resolution,[],[f158,f2330])).

fof(f2330,plain,(
    ! [X4,X2,X3] :
      ( v2_compts_1(X3,X4)
      | ~ v2_compts_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(sK2(X4,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))
      | ~ v1_tops_2(sK2(X4,X3),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | m1_subset_1(sK3(X2,X3,sK2(X4,X3)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f1330,f105])).

fof(f1330,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_setfam_1(X8,X7)
      | m1_subset_1(sK3(X6,X7,X8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
      | ~ v2_compts_1(X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))))
      | ~ v1_tops_2(X8,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f1326,f111])).

fof(f1326,plain,(
    ! [X6,X8,X7] :
      ( m1_subset_1(sK3(X6,X7,X8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
      | ~ m1_setfam_1(X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
      | ~ v2_compts_1(X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))))
      | ~ v1_tops_2(X8,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(duplicate_literal_removal,[],[f1325])).

fof(f1325,plain,(
    ! [X6,X8,X7] :
      ( m1_subset_1(sK3(X6,X7,X8),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
      | ~ m1_setfam_1(X8,X7)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
      | ~ v2_compts_1(X7,X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))))
      | ~ v1_tops_2(X8,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f100,f110])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_tops_2(X4,X0)
      | m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_setfam_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f14030,plain,
    ( ~ spl10_23
    | ~ spl10_7
    | spl10_432
    | spl10_5 ),
    inference(avatar_split_clause,[],[f14022,f157,f3914,f163,f285])).

fof(f14022,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(X0,sK1,sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
        | ~ m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v1_tops_2(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl10_5 ),
    inference(resolution,[],[f158,f1021])).

fof(f1021,plain,(
    ! [X4,X2,X3] :
      ( v2_compts_1(X3,X2)
      | r1_tarski(sK3(X4,X3,sK2(X2,X3)),sK2(X2,X3))
      | ~ m1_subset_1(sK2(X2,X3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X4))))
      | ~ v2_compts_1(X3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ v1_tops_2(sK2(X2,X3),X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f101,f105])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_setfam_1(X4,X1)
      | ~ v1_tops_2(X4,X0)
      | r1_tarski(sK3(X0,X1,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f14028,plain,
    ( ~ spl10_23
    | ~ spl10_7
    | spl10_436
    | spl10_5 ),
    inference(avatar_split_clause,[],[f14020,f157,f3932,f163,f285])).

fof(f14020,plain,
    ( m1_subset_1(sK2(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_5 ),
    inference(resolution,[],[f158,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f11965,plain,
    ( ~ spl10_78
    | spl10_85 ),
    inference(avatar_contradiction_clause,[],[f11964])).

fof(f11964,plain,
    ( $false
    | ~ spl10_78
    | ~ spl10_85 ),
    inference(subsumption_resolution,[],[f977,f911])).

fof(f911,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1)))
    | ~ spl10_78 ),
    inference(avatar_component_clause,[],[f910])).

fof(f910,plain,
    ( spl10_78
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f977,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1)))
    | ~ spl10_85 ),
    inference(resolution,[],[f934,f98])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',dt_u1_pre_topc)).

fof(f934,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))))))
    | ~ spl10_85 ),
    inference(avatar_component_clause,[],[f933])).

fof(f933,plain,
    ( spl10_85
  <=> ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_85])])).

fof(f11933,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | spl10_1605 ),
    inference(avatar_contradiction_clause,[],[f11932])).

fof(f11932,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_1605 ),
    inference(subsumption_resolution,[],[f11931,f89])).

fof(f11931,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_1605 ),
    inference(subsumption_resolution,[],[f11930,f149])).

fof(f11930,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_1605 ),
    inference(subsumption_resolution,[],[f11928,f146])).

fof(f146,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f145])).

fof(f11928,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_1605 ),
    inference(resolution,[],[f11918,f106])).

fof(f11918,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),sK0)
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_1605 ),
    inference(subsumption_resolution,[],[f11917,f87])).

fof(f11917,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_1605 ),
    inference(subsumption_resolution,[],[f11916,f88])).

fof(f11916,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_1605 ),
    inference(subsumption_resolution,[],[f11915,f89])).

fof(f11915,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_1605 ),
    inference(subsumption_resolution,[],[f11913,f1656])).

fof(f1656,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88 ),
    inference(backward_demodulation,[],[f1652,f1575])).

fof(f1575,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_84
    | ~ spl10_86 ),
    inference(backward_demodulation,[],[f1572,f931])).

fof(f931,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))))))
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f930])).

fof(f930,plain,
    ( spl10_84
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f1572,plain,
    ( u1_struct_0(sK0) = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1)))
    | ~ spl10_86 ),
    inference(equality_resolution,[],[f939])).

fof(f939,plain,
    ( ! [X2,X1] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))) = X1 )
    | ~ spl10_86 ),
    inference(avatar_component_clause,[],[f938])).

fof(f938,plain,
    ( spl10_86
  <=> ! [X1,X2] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f1652,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))) = sK2(sK0,sK1)
    | ~ spl10_88 ),
    inference(equality_resolution,[],[f943])).

fof(f943,plain,
    ( ! [X6,X5] :
        ( g1_pre_topc(X5,X6) != g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))) = X6 )
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f942])).

fof(f942,plain,
    ( spl10_88
  <=> ! [X5,X6] :
        ( g1_pre_topc(X5,X6) != g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f11913,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_1605 ),
    inference(resolution,[],[f11852,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f11852,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1605 ),
    inference(avatar_component_clause,[],[f11851])).

fof(f11851,plain,
    ( spl10_1605
  <=> ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1605])])).

fof(f11912,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | spl10_1607 ),
    inference(avatar_contradiction_clause,[],[f11911])).

fof(f11911,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11910,f89])).

fof(f11910,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11909,f149])).

fof(f11909,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11907,f146])).

fof(f11907,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(resolution,[],[f11897,f106])).

fof(f11897,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11896,f87])).

fof(f11896,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11895,f88])).

fof(f11895,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11894,f89])).

fof(f11894,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11892,f1656])).

fof(f11892,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(resolution,[],[f11889,f108])).

fof(f11889,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11888,f149])).

fof(f11888,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(forward_demodulation,[],[f11887,f1828])).

fof(f11887,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11886,f1656])).

fof(f11886,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(forward_demodulation,[],[f11885,f1828])).

fof(f11885,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11884,f283])).

fof(f11884,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_4
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11883,f155])).

fof(f155,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl10_4
  <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f11883,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_848
    | ~ spl10_1607 ),
    inference(subsumption_resolution,[],[f11882,f6825])).

fof(f6825,plain,
    ( m1_setfam_1(sK2(sK0,sK1),sK1)
    | ~ spl10_848 ),
    inference(avatar_component_clause,[],[f6824])).

fof(f6824,plain,
    ( spl10_848
  <=> m1_setfam_1(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_848])])).

fof(f11882,plain,
    ( ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_setfam_1(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1607 ),
    inference(resolution,[],[f11858,f102])).

fof(f11858,plain,
    ( ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ spl10_1607 ),
    inference(avatar_component_clause,[],[f11857])).

fof(f11857,plain,
    ( spl10_1607
  <=> ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1607])])).

fof(f11859,plain,
    ( ~ spl10_1605
    | ~ spl10_1607
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(avatar_split_clause,[],[f11846,f6824,f1744,f942,f938,f930,f282,f154,f148,f145,f11857,f11851])).

fof(f11846,plain,
    ( ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f11845,f149])).

fof(f11845,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(forward_demodulation,[],[f11844,f1828])).

fof(f11844,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f11843,f1656])).

fof(f11843,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(forward_demodulation,[],[f11842,f1828])).

fof(f11842,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f11841,f89])).

fof(f11841,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f11840,f149])).

fof(f11840,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f11839,f6866])).

fof(f6866,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(forward_demodulation,[],[f6865,f1828])).

fof(f6865,plain,
    ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f6864,f149])).

fof(f6864,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(forward_demodulation,[],[f6863,f1828])).

fof(f6863,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f6862,f149])).

fof(f6862,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f6861,f146])).

fof(f6861,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f6860,f87])).

fof(f6860,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f6859,f88])).

fof(f6859,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f6858,f89])).

fof(f6858,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f6857,f283])).

fof(f6857,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f6852,f155])).

fof(f6852,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_848 ),
    inference(resolution,[],[f6825,f2387])).

fof(f2387,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_setfam_1(sK2(X0,X1),X2)
      | ~ v2_compts_1(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2,sK2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f2386,f104])).

fof(f2386,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_setfam_1(sK2(X0,X1),X2)
      | ~ v2_compts_1(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2,sK2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f2382])).

fof(f2382,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_setfam_1(sK2(X0,X1),X2)
      | ~ v2_compts_1(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(sK2(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X2,sK2(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_compts_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f1329,f106])).

fof(f1329,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_tops_2(X5,X3)
      | ~ m1_setfam_1(X5,X4)
      | ~ v2_compts_1(X4,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
      | m1_subset_1(sK3(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4,X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f1324,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1324,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(sK3(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)),X4,X5),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
      | ~ m1_setfam_1(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
      | ~ v2_compts_1(X4,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
      | ~ v1_tops_2(X5,X3)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f100,f108])).

fof(f11839,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f11838,f146])).

fof(f11838,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | v2_compts_1(sK1,sK0)
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f11837,f283])).

fof(f11837,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0)
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f11836,f155])).

fof(f11836,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0)
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218
    | ~ spl10_848 ),
    inference(subsumption_resolution,[],[f11832,f6825])).

fof(f11832,plain,
    ( ~ m1_setfam_1(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0)
    | ~ m1_setfam_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK1)
    | ~ v1_tops_2(sK2(sK0,sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218 ),
    inference(resolution,[],[f8208,f875])).

fof(f8208,plain,
    ( r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218 ),
    inference(subsumption_resolution,[],[f8207,f149])).

fof(f8207,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88
    | ~ spl10_218 ),
    inference(forward_demodulation,[],[f8206,f1828])).

fof(f8206,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f8205,f149])).

fof(f8205,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f8204,f146])).

fof(f8204,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f8203,f87])).

fof(f8203,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f8202,f88])).

fof(f8202,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f8201,f89])).

fof(f8201,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f8200,f155])).

fof(f8200,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_22
    | ~ spl10_84
    | ~ spl10_86
    | ~ spl10_88 ),
    inference(subsumption_resolution,[],[f8199,f1656])).

fof(f8199,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f8198,f283])).

fof(f8198,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(duplicate_literal_removal,[],[f8194])).

fof(f8194,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | r1_tarski(sK3(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f4366,f106])).

fof(f4366,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | r1_tarski(sK3(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f4362,f109])).

fof(f4362,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | r1_tarski(sK3(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v1_tops_2(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f4133,f108])).

fof(f4133,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | r1_tarski(sK3(X0,sK1,sK2(sK0,sK1)),sK2(sK0,sK1)) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f4132,f89])).

fof(f4132,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(X0,sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v1_tops_2(sK2(sK0,sK1),X0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f4129,f149])).

fof(f4129,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(X0,sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
        | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v1_tops_2(sK2(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl10_1 ),
    inference(resolution,[],[f146,f1021])).

fof(f6851,plain,
    ( spl10_1
    | ~ spl10_2
    | spl10_849 ),
    inference(avatar_contradiction_clause,[],[f6850])).

fof(f6850,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_849 ),
    inference(subsumption_resolution,[],[f6849,f89])).

fof(f6849,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_849 ),
    inference(subsumption_resolution,[],[f6848,f149])).

fof(f6848,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_849 ),
    inference(subsumption_resolution,[],[f6847,f146])).

fof(f6847,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_849 ),
    inference(resolution,[],[f6828,f105])).

fof(f6828,plain,
    ( ~ m1_setfam_1(sK2(sK0,sK1),sK1)
    | ~ spl10_849 ),
    inference(avatar_component_clause,[],[f6827])).

fof(f6827,plain,
    ( spl10_849
  <=> ~ m1_setfam_1(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_849])])).

fof(f3973,plain,
    ( ~ spl10_2
    | spl10_7
    | ~ spl10_218 ),
    inference(avatar_contradiction_clause,[],[f3972])).

fof(f3972,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_7
    | ~ spl10_218 ),
    inference(subsumption_resolution,[],[f3963,f149])).

fof(f3963,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_7
    | ~ spl10_218 ),
    inference(backward_demodulation,[],[f1828,f164])).

fof(f164,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f163])).

fof(f1798,plain,
    ( ~ spl10_22
    | spl10_215 ),
    inference(avatar_contradiction_clause,[],[f1797])).

fof(f1797,plain,
    ( $false
    | ~ spl10_22
    | ~ spl10_215 ),
    inference(subsumption_resolution,[],[f1794,f283])).

fof(f1794,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_215 ),
    inference(resolution,[],[f1735,f98])).

fof(f1735,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
    | ~ spl10_215 ),
    inference(avatar_component_clause,[],[f1734])).

fof(f1734,plain,
    ( spl10_215
  <=> ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_215])])).

fof(f1746,plain,
    ( ~ spl10_215
    | spl10_218 ),
    inference(avatar_split_clause,[],[f1718,f1744,f1734])).

fof(f1718,plain,(
    ! [X2,X1] :
      ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))
      | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = X1
      | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) ) ),
    inference(superposition,[],[f126,f1704])).

fof(f1704,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(resolution,[],[f1651,f89])).

fof(f1651,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) ) ),
    inference(global_subsumption,[],[f884])).

fof(f884,plain,(
    ! [X5] :
      ( g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))),u1_pre_topc(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))))
      | ~ l1_pre_topc(X5) ) ),
    inference(resolution,[],[f217,f98])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f213,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',dt_g1_pre_topc)).

fof(f213,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) = g1_pre_topc(u1_struct_0(g1_pre_topc(X0,X1)),u1_pre_topc(g1_pre_topc(X0,X1)))
      | ~ l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f99,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',abstractness_v1_pre_topc)).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t33_compts_1.p',free_g1_pre_topc)).

fof(f967,plain,
    ( spl10_1
    | ~ spl10_2
    | spl10_79 ),
    inference(avatar_contradiction_clause,[],[f966])).

fof(f966,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_79 ),
    inference(subsumption_resolution,[],[f965,f564])).

fof(f564,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f563,f89])).

fof(f563,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f562,f149])).

fof(f562,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl10_1 ),
    inference(resolution,[],[f104,f146])).

fof(f965,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_79 ),
    inference(resolution,[],[f914,f125])).

fof(f914,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1)))
    | ~ spl10_79 ),
    inference(avatar_component_clause,[],[f913])).

fof(f913,plain,
    ( spl10_79
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f944,plain,
    ( ~ spl10_85
    | spl10_88
    | spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f899,f148,f145,f942,f933])).

fof(f899,plain,
    ( ! [X6,X5] :
        ( g1_pre_topc(X5,X6) != g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))
        | u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))) = X6
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1)))))) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(superposition,[],[f127,f887])).

fof(f887,plain,
    ( g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))))
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(resolution,[],[f217,f564])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f940,plain,
    ( ~ spl10_85
    | spl10_86
    | spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f897,f148,f145,f938,f933])).

fof(f897,plain,
    ( ! [X2,X1] :
        ( g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))) = X1
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),sK2(sK0,sK1)))))) )
    | ~ spl10_1
    | ~ spl10_2 ),
    inference(superposition,[],[f126,f887])).

fof(f312,plain,(
    spl10_23 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl10_23 ),
    inference(subsumption_resolution,[],[f308,f89])).

fof(f308,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl10_23 ),
    inference(resolution,[],[f305,f98])).

fof(f305,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_23 ),
    inference(resolution,[],[f286,f125])).

fof(f286,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f285])).

fof(f169,plain,
    ( spl10_0
    | spl10_4 ),
    inference(avatar_split_clause,[],[f90,f154,f142])).

fof(f90,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f166,plain,
    ( spl10_2
    | spl10_6 ),
    inference(avatar_split_clause,[],[f93,f160,f148])).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

fof(f165,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f94,f163,f157,f151,f145])).

fof(f94,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).
%------------------------------------------------------------------------------
