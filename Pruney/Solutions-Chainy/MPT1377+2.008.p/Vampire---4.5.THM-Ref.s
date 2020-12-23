%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 694 expanded)
%              Number of leaves         :   24 ( 195 expanded)
%              Depth                    :   23
%              Number of atoms          :  550 (3668 expanded)
%              Number of equality atoms :   17 (  85 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1067,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f75,f78,f126,f133,f138,f366,f615,f631,f635,f926,f934,f1000,f1066])).

fof(f1066,plain,
    ( spl2_2
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(avatar_contradiction_clause,[],[f1065])).

fof(f1065,plain,
    ( $false
    | spl2_2
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(subsumption_resolution,[],[f816,f65])).

fof(f65,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f816,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f815,f55])).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f815,plain,
    ( m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(resolution,[],[f760,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f760,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_8
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f750,f132])).

fof(f132,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl2_8
  <=> sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f750,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))))
        | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_20 ),
    inference(resolution,[],[f266,f87])).

fof(f87,plain,(
    ! [X8,X7] :
      ( ~ m1_pre_topc(X8,sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8)))
      | m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
      | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_compts_1(sK1,sK0) )
    & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
      | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v2_compts_1(sK1,sK0) ) )
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f32,plain,
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
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v2_compts_1(X1,sK0) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
            | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
              & v2_compts_1(X1,sK0) ) ) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          | ~ v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v2_compts_1(X1,sK0) )
        & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
          | ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            & v2_compts_1(X1,sK0) ) ) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
        | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_compts_1(sK1,sK0) )
      & ( ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
          & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
        | ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v2_compts_1(sK1,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <~> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v2_compts_1(X1,X0) )
          <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v2_compts_1(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).

fof(f266,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl2_20
  <=> m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f1000,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f999])).

fof(f999,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f998,f103])).

fof(f103,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_5
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f998,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(subsumption_resolution,[],[f991,f69])).

fof(f69,plain,
    ( ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_3
  <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f991,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f581,f208])).

fof(f208,plain,(
    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f207,f169])).

fof(f169,plain,(
    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f167,f55])).

fof(f167,plain,(
    l1_pre_topc(k1_pre_topc(sK0,k2_subset_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f97,f53])).

fof(f97,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k1_pre_topc(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f95,f37])).

fof(f95,plain,(
    ! [X2] :
      ( l1_pre_topc(k1_pre_topc(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f88,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f88,plain,(
    ! [X9] :
      ( ~ m1_pre_topc(X9,sK0)
      | l1_pre_topc(X9) ) ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f207,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f203,f37])).

fof(f203,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(resolution,[],[f197,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f197,plain,(
    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0) ),
    inference(forward_demodulation,[],[f195,f55])).

fof(f195,plain,(
    m1_pre_topc(k1_pre_topc(sK0,k2_subset_1(u1_struct_0(sK0))),sK0) ),
    inference(resolution,[],[f85,f53])).

fof(f85,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_pre_topc(k1_pre_topc(sK0,X5),sK0) ) ),
    inference(resolution,[],[f37,f48])).

fof(f581,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X1)
        | v2_compts_1(sK1,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f580,f64])).

fof(f64,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f580,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(sK1,X1)
        | ~ m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f579,f276])).

fof(f276,plain,(
    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f274,f55])).

fof(f274,plain,(
    k2_subset_1(u1_struct_0(sK0)) = u1_struct_0(k1_pre_topc(sK0,k2_subset_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f86,f53])).

fof(f86,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(k1_pre_topc(sK0,X6)) = X6 ) ),
    inference(resolution,[],[f37,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f579,plain,
    ( ! [X1] :
        ( v2_compts_1(sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
        | ~ m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f575,f52])).

fof(f575,plain,
    ( ! [X1] :
        ( v2_compts_1(sK1,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f571,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | ~ v2_compts_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X2,X0)
      | ~ v2_compts_1(X3,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_compts_1(X2,X0)
                      | ~ v2_compts_1(X3,X1) )
                    & ( v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <=> v2_compts_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

fof(f571,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f570,f64])).

fof(f570,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f564,f276])).

fof(f564,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
    | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_1 ),
    inference(resolution,[],[f442,f197])).

fof(f442,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_compts_1(sK1,X0) )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f441,f87])).

fof(f441,plain,
    ( ! [X0] :
        ( v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f439,f37])).

fof(f439,plain,
    ( ! [X0] :
        ( v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f60,f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f60,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_1
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f934,plain,
    ( ~ spl2_3
    | spl2_6
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f933,f102,f71,f106,f67])).

fof(f106,plain,
    ( spl2_6
  <=> ! [X0] :
        ( v2_compts_1(sK1,X0)
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f71,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f933,plain,
    ( ! [X4] :
        ( v2_compts_1(sK1,X4)
        | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ m1_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f703,f103])).

fof(f703,plain,
    ( ! [X4] :
        ( v2_compts_1(sK1,X4)
        | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X4)))
        | ~ m1_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f72,f57])).

fof(f72,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f926,plain,
    ( ~ spl2_2
    | ~ spl2_6
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f925])).

fof(f925,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f924,f64])).

fof(f924,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f923,f276])).

fof(f923,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f920,f197])).

fof(f920,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_26 ),
    inference(resolution,[],[f916,f630])).

fof(f630,plain,
    ( ! [X2] :
        ( ~ v2_compts_1(sK1,X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) )
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f629])).

fof(f629,plain,
    ( spl2_26
  <=> ! [X2] :
        ( ~ v2_compts_1(sK1,X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f916,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f915,f64])).

fof(f915,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f906,f276])).

fof(f906,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))))
    | ~ spl2_6 ),
    inference(resolution,[],[f107,f208])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f635,plain,
    ( ~ spl2_10
    | spl2_20
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f423,f135,f265,f223])).

fof(f223,plain,
    ( spl2_10
  <=> l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f135,plain,
    ( spl2_9
  <=> m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f423,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f416,f37])).

fof(f416,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ spl2_9 ),
    inference(resolution,[],[f137,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f137,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f631,plain,
    ( spl2_26
    | spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f627,f63,f59,f629])).

fof(f627,plain,
    ( ! [X2] :
        ( v2_compts_1(sK1,sK0)
        | ~ v2_compts_1(sK1,X2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f455,f37])).

fof(f455,plain,
    ( ! [X2] :
        ( v2_compts_1(sK1,sK0)
        | ~ v2_compts_1(sK1,X2)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_pre_topc(X2,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f64,f56])).

fof(f615,plain,
    ( ~ spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f614])).

fof(f614,plain,
    ( $false
    | ~ spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f613,f208])).

fof(f613,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f610,f64])).

fof(f610,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f476,f276])).

fof(f476,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f475,f103])).

fof(f475,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) )
    | spl2_4 ),
    inference(resolution,[],[f73,f52])).

fof(f73,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f366,plain,
    ( ~ spl2_4
    | ~ spl2_5
    | spl2_10 ),
    inference(avatar_contradiction_clause,[],[f365])).

fof(f365,plain,
    ( $false
    | ~ spl2_4
    | ~ spl2_5
    | spl2_10 ),
    inference(subsumption_resolution,[],[f364,f72])).

fof(f364,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ spl2_5
    | spl2_10 ),
    inference(subsumption_resolution,[],[f363,f103])).

fof(f363,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | spl2_10 ),
    inference(duplicate_literal_removal,[],[f357])).

fof(f357,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_10 ),
    inference(resolution,[],[f277,f48])).

fof(f277,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl2_10 ),
    inference(resolution,[],[f225,f54])).

fof(f225,plain,
    ( ~ l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f223])).

fof(f138,plain,
    ( ~ spl2_5
    | spl2_9
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f116,f71,f135,f102])).

fof(f116,plain,
    ( m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f72,f48])).

fof(f133,plain,
    ( ~ spl2_5
    | spl2_8
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f117,f71,f130,f102])).

fof(f117,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_4 ),
    inference(resolution,[],[f72,f49])).

fof(f126,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f124,f104])).

fof(f104,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f124,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f84,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f37,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f78,plain,
    ( spl2_1
    | spl2_3 ),
    inference(avatar_split_clause,[],[f38,f67,f59])).

fof(f38,plain,
    ( v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,
    ( spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f41,f71,f63])).

fof(f41,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f42,f71,f67,f63,f59])).

fof(f42,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))
    | ~ v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (19267)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (19268)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (19279)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (19281)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (19276)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (19269)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (19283)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (19271)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (19280)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (19284)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (19265)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (19278)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (19266)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (19270)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (19272)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (19282)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (19274)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (19273)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (19285)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (19277)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (19275)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.54  % (19284)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1067,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f74,f75,f78,f126,f133,f138,f366,f615,f631,f635,f926,f934,f1000,f1066])).
% 0.21/0.54  fof(f1066,plain,(
% 0.21/0.54    spl2_2 | ~spl2_8 | ~spl2_20),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1065])).
% 0.21/0.54  fof(f1065,plain,(
% 0.21/0.54    $false | (spl2_2 | ~spl2_8 | ~spl2_20)),
% 0.21/0.54    inference(subsumption_resolution,[],[f816,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.54  fof(f816,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_8 | ~spl2_20)),
% 0.21/0.54    inference(forward_demodulation,[],[f815,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.54  fof(f815,plain,(
% 0.21/0.54    m1_subset_1(k2_subset_1(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_8 | ~spl2_20)),
% 0.21/0.54    inference(resolution,[],[f760,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.54  fof(f760,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK1)) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_8 | ~spl2_20)),
% 0.21/0.54    inference(forward_demodulation,[],[f750,f132])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f130])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    spl2_8 <=> sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.54  fof(f750,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_20),
% 0.21/0.54    inference(resolution,[],[f266,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X8,X7] : (~m1_pre_topc(X8,sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8))) | m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.54    inference(resolution,[],[f37,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(X1,sK0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(X1,sK0)))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)) & ((m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) & v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v2_compts_1(sK1,sK0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0)) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_compts_1(X1,X0))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)))) & l1_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <~> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_compts_1(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v2_compts_1(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_compts_1)).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~spl2_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f265])).
% 0.21/0.54  fof(f265,plain,(
% 0.21/0.54    spl2_20 <=> m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.54  fof(f1000,plain,(
% 0.21/0.54    ~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f999])).
% 0.21/0.54  fof(f999,plain,(
% 0.21/0.54    $false | (~spl2_1 | ~spl2_2 | spl2_3 | ~spl2_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f998,f103])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    spl2_5 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.54  fof(f998,plain,(
% 0.21/0.54    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_1 | ~spl2_2 | spl2_3)),
% 0.21/0.54    inference(subsumption_resolution,[],[f991,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl2_3 <=> v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.54  fof(f991,plain,(
% 0.21/0.54    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_1 | ~spl2_2)),
% 0.21/0.54    inference(resolution,[],[f581,f208])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f207,f169])).
% 0.21/0.54  fof(f169,plain,(
% 0.21/0.54    l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.21/0.54    inference(forward_demodulation,[],[f167,f55])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    l1_pre_topc(k1_pre_topc(sK0,k2_subset_1(u1_struct_0(sK0))))),
% 0.21/0.54    inference(resolution,[],[f97,f53])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k1_pre_topc(sK0,X2))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f95,f37])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X2] : (l1_pre_topc(k1_pre_topc(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.54    inference(resolution,[],[f88,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.21/0.54    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X9] : (~m1_pre_topc(X9,sK0) | l1_pre_topc(X9)) )),
% 0.21/0.54    inference(resolution,[],[f37,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.21/0.54    inference(subsumption_resolution,[],[f203,f37])).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.21/0.54    inference(resolution,[],[f197,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.21/0.54  fof(f197,plain,(
% 0.21/0.54    m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f195,f55])).
% 0.21/0.54  fof(f195,plain,(
% 0.21/0.54    m1_pre_topc(k1_pre_topc(sK0,k2_subset_1(u1_struct_0(sK0))),sK0)),
% 0.21/0.54    inference(resolution,[],[f85,f53])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(k1_pre_topc(sK0,X5),sK0)) )),
% 0.21/0.54    inference(resolution,[],[f37,f48])).
% 0.21/0.54  fof(f581,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X1) | v2_compts_1(sK1,X1) | ~l1_pre_topc(X1)) ) | (~spl2_1 | ~spl2_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f580,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f63])).
% 0.21/0.54  fof(f580,plain,(
% 0.21/0.54    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(sK1,X1) | ~m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X1) | ~l1_pre_topc(X1)) ) | (~spl2_1 | ~spl2_2)),
% 0.21/0.54    inference(forward_demodulation,[],[f579,f276])).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    u1_struct_0(sK0) = u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.21/0.54    inference(forward_demodulation,[],[f274,f55])).
% 0.21/0.54  fof(f274,plain,(
% 0.21/0.54    k2_subset_1(u1_struct_0(sK0)) = u1_struct_0(k1_pre_topc(sK0,k2_subset_1(u1_struct_0(sK0))))),
% 0.21/0.54    inference(resolution,[],[f86,f53])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X6)) = X6) )),
% 0.21/0.54    inference(resolution,[],[f37,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.21/0.54  fof(f579,plain,(
% 0.21/0.54    ( ! [X1] : (v2_compts_1(sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X1) | ~l1_pre_topc(X1)) ) | (~spl2_1 | ~spl2_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f575,f52])).
% 0.21/0.54  fof(f575,plain,(
% 0.21/0.54    ( ! [X1] : (v2_compts_1(sK1,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),X1) | ~l1_pre_topc(X1)) ) | (~spl2_1 | ~spl2_2)),
% 0.21/0.54    inference(resolution,[],[f571,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | ~v2_compts_1(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) | ~v2_compts_1(X3,X1)) & (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).
% 0.21/0.54  fof(f571,plain,(
% 0.21/0.54    v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | (~spl2_1 | ~spl2_2)),
% 0.21/0.54    inference(subsumption_resolution,[],[f570,f64])).
% 0.21/0.54  fof(f570,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~spl2_1),
% 0.21/0.54    inference(forward_demodulation,[],[f564,f276])).
% 0.21/0.54  fof(f564,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~spl2_1),
% 0.21/0.54    inference(resolution,[],[f442,f197])).
% 0.21/0.54  fof(f442,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK1,X0)) ) | ~spl2_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f441,f87])).
% 0.21/0.54  fof(f441,plain,(
% 0.21/0.54    ( ! [X0] : (v2_compts_1(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK0)) ) | ~spl2_1),
% 0.21/0.54    inference(subsumption_resolution,[],[f439,f37])).
% 0.21/0.54  fof(f439,plain,(
% 0.21/0.54    ( ! [X0] : (v2_compts_1(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) ) | ~spl2_1),
% 0.21/0.54    inference(resolution,[],[f60,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f36])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    v2_compts_1(sK1,sK0) | ~spl2_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl2_1 <=> v2_compts_1(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.54  fof(f934,plain,(
% 0.21/0.54    ~spl2_3 | spl2_6 | ~spl2_4 | ~spl2_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f933,f102,f71,f106,f67])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    spl2_6 <=> ! [X0] : (v2_compts_1(sK1,X0) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.54  fof(f933,plain,(
% 0.21/0.54    ( ! [X4] : (v2_compts_1(sK1,X4) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X4))) | ~m1_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | (~spl2_4 | ~spl2_5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f703,f103])).
% 0.21/0.54  fof(f703,plain,(
% 0.21/0.54    ( ! [X4] : (v2_compts_1(sK1,X4) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X4))) | ~m1_pre_topc(X4,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | ~spl2_4),
% 0.21/0.54    inference(resolution,[],[f72,f57])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~spl2_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f71])).
% 0.21/0.54  fof(f926,plain,(
% 0.21/0.54    ~spl2_2 | ~spl2_6 | ~spl2_26),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f925])).
% 0.21/0.54  fof(f925,plain,(
% 0.21/0.54    $false | (~spl2_2 | ~spl2_6 | ~spl2_26)),
% 0.21/0.54    inference(subsumption_resolution,[],[f924,f64])).
% 0.21/0.54  fof(f924,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_6 | ~spl2_26)),
% 0.21/0.54    inference(forward_demodulation,[],[f923,f276])).
% 0.21/0.54  fof(f923,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | (~spl2_2 | ~spl2_6 | ~spl2_26)),
% 0.21/0.54    inference(subsumption_resolution,[],[f920,f197])).
% 0.21/0.54  fof(f920,plain,(
% 0.21/0.54    ~m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | (~spl2_2 | ~spl2_6 | ~spl2_26)),
% 0.21/0.54    inference(resolution,[],[f916,f630])).
% 0.21/0.54  fof(f630,plain,(
% 0.21/0.54    ( ! [X2] : (~v2_compts_1(sK1,X2) | ~m1_pre_topc(X2,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))) ) | ~spl2_26),
% 0.21/0.54    inference(avatar_component_clause,[],[f629])).
% 0.21/0.54  fof(f629,plain,(
% 0.21/0.54    spl2_26 <=> ! [X2] : (~v2_compts_1(sK1,X2) | ~m1_pre_topc(X2,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.54  fof(f916,plain,(
% 0.21/0.54    v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | (~spl2_2 | ~spl2_6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f915,f64])).
% 0.21/0.54  fof(f915,plain,(
% 0.21/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~spl2_6),
% 0.21/0.54    inference(forward_demodulation,[],[f906,f276])).
% 0.21/0.54  fof(f906,plain,(
% 0.21/0.54    v2_compts_1(sK1,k1_pre_topc(sK0,u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,u1_struct_0(sK0))))) | ~spl2_6),
% 0.21/0.54    inference(resolution,[],[f107,f208])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl2_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f106])).
% 0.21/0.54  fof(f635,plain,(
% 0.21/0.54    ~spl2_10 | spl2_20 | ~spl2_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f423,f135,f265,f223])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    spl2_10 <=> l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    spl2_9 <=> m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.54  fof(f423,plain,(
% 0.21/0.54    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_9),
% 0.21/0.54    inference(subsumption_resolution,[],[f416,f37])).
% 0.21/0.54  fof(f416,plain,(
% 0.21/0.54    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~spl2_9),
% 0.21/0.54    inference(resolution,[],[f137,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f135])).
% 0.21/0.55  fof(f631,plain,(
% 0.21/0.55    spl2_26 | spl2_1 | ~spl2_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f627,f63,f59,f629])).
% 0.21/0.55  fof(f627,plain,(
% 0.21/0.55    ( ! [X2] : (v2_compts_1(sK1,sK0) | ~v2_compts_1(sK1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X2,sK0)) ) | ~spl2_2),
% 0.21/0.55    inference(subsumption_resolution,[],[f455,f37])).
% 0.21/0.55  fof(f455,plain,(
% 0.21/0.55    ( ! [X2] : (v2_compts_1(sK1,sK0) | ~v2_compts_1(sK1,X2) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_pre_topc(X2,sK0) | ~l1_pre_topc(sK0)) ) | ~spl2_2),
% 0.21/0.55    inference(resolution,[],[f64,f56])).
% 0.21/0.55  fof(f615,plain,(
% 0.21/0.55    ~spl2_2 | spl2_4 | ~spl2_5),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f614])).
% 0.21/0.55  fof(f614,plain,(
% 0.21/0.55    $false | (~spl2_2 | spl2_4 | ~spl2_5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f613,f208])).
% 0.21/0.55  fof(f613,plain,(
% 0.21/0.55    ~m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl2_2 | spl2_4 | ~spl2_5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f610,f64])).
% 0.21/0.55  fof(f610,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(k1_pre_topc(sK0,u1_struct_0(sK0)),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (spl2_4 | ~spl2_5)),
% 0.21/0.55    inference(superposition,[],[f476,f276])).
% 0.21/0.55  fof(f476,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | (spl2_4 | ~spl2_5)),
% 0.21/0.55    inference(subsumption_resolution,[],[f475,f103])).
% 0.21/0.55  fof(f475,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ) | spl2_4),
% 0.21/0.55    inference(resolution,[],[f73,f52])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | spl2_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f71])).
% 0.21/0.55  fof(f366,plain,(
% 0.21/0.55    ~spl2_4 | ~spl2_5 | spl2_10),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f365])).
% 0.21/0.55  fof(f365,plain,(
% 0.21/0.55    $false | (~spl2_4 | ~spl2_5 | spl2_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f364,f72])).
% 0.21/0.55  fof(f364,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | (~spl2_5 | spl2_10)),
% 0.21/0.55    inference(subsumption_resolution,[],[f363,f103])).
% 0.21/0.55  fof(f363,plain,(
% 0.21/0.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | spl2_10),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f357])).
% 0.21/0.55  fof(f357,plain,(
% 0.21/0.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_10),
% 0.21/0.55    inference(resolution,[],[f277,f48])).
% 0.21/0.55  fof(f277,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),X0) | ~l1_pre_topc(X0)) ) | spl2_10),
% 0.21/0.55    inference(resolution,[],[f225,f54])).
% 0.21/0.55  fof(f225,plain,(
% 0.21/0.55    ~l1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | spl2_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f223])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    ~spl2_5 | spl2_9 | ~spl2_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f116,f71,f135,f102])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    m1_pre_topc(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1),g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.55    inference(resolution,[],[f72,f48])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    ~spl2_5 | spl2_8 | ~spl2_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f117,f71,f130,f102])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    sK1 = u1_struct_0(k1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_4),
% 0.21/0.55    inference(resolution,[],[f72,f49])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    spl2_5),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f125])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    $false | spl2_5),
% 0.21/0.55    inference(subsumption_resolution,[],[f124,f104])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl2_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f102])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.21/0.55    inference(resolution,[],[f84,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.55    inference(resolution,[],[f37,f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    spl2_1 | spl2_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f38,f67,f59])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_compts_1(sK1,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    spl2_2 | spl2_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f41,f71,f63])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f42,f71,f67,f63,f59])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))) | ~v2_compts_1(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_compts_1(sK1,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (19284)------------------------------
% 0.21/0.55  % (19284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (19284)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (19284)Memory used [KB]: 6524
% 0.21/0.55  % (19284)Time elapsed: 0.131 s
% 0.21/0.55  % (19284)------------------------------
% 0.21/0.55  % (19284)------------------------------
% 0.21/0.55  % (19264)Success in time 0.187 s
%------------------------------------------------------------------------------
