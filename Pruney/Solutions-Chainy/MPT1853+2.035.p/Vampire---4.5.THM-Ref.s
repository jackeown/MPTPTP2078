%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 701 expanded)
%              Number of leaves         :   35 ( 208 expanded)
%              Depth                    :   17
%              Number of atoms          :  579 (3722 expanded)
%              Number of equality atoms :   40 (  71 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f921,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f102,f117,f160,f169,f193,f199,f204,f278,f310,f329,f354,f449,f754,f834,f838,f855,f890,f920])).

fof(f920,plain,
    ( spl4_11
    | ~ spl4_30
    | ~ spl4_61 ),
    inference(avatar_contradiction_clause,[],[f919])).

fof(f919,plain,
    ( $false
    | spl4_11
    | ~ spl4_30
    | ~ spl4_61 ),
    inference(subsumption_resolution,[],[f756,f168])).

fof(f168,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl4_11
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f756,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_30
    | ~ spl4_61 ),
    inference(backward_demodulation,[],[f309,f692])).

fof(f692,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f690])).

fof(f690,plain,
    ( spl4_61
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f309,plain,
    ( v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl4_30
  <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f890,plain,
    ( spl4_1
    | ~ spl4_40
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f889,f247,f444,f94])).

fof(f94,plain,
    ( spl4_1
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f444,plain,
    ( spl4_40
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f247,plain,
    ( spl4_20
  <=> sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f889,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f888,f63])).

fof(f63,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
            | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | ~ v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          | v1_tex_2(k1_tex_2(sK0,X1),sK0) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | v1_tex_2(k1_tex_2(sK0,sK1),sK0) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f888,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f683,f186])).

fof(f186,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f185,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f185,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f177,f63])).

fof(f177,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f64,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f64,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f683,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_20 ),
    inference(superposition,[],[f75,f249])).

fof(f249,plain,
    ( sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f247])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f855,plain,
    ( ~ spl4_11
    | ~ spl4_40
    | spl4_4
    | spl4_23 ),
    inference(avatar_split_clause,[],[f854,f275,f114,f444,f166])).

fof(f114,plain,
    ( spl4_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f275,plain,
    ( spl4_23
  <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f854,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl4_4
    | spl4_23 ),
    inference(subsumption_resolution,[],[f751,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f751,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl4_23 ),
    inference(subsumption_resolution,[],[f744,f277])).

fof(f277,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f275])).

fof(f744,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f330,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f330,plain,(
    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f320,f63])).

fof(f320,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f186,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f838,plain,
    ( spl4_12
    | spl4_2
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f407,f201,f98,f196])).

fof(f196,plain,
    ( spl4_12
  <=> u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f98,plain,
    ( spl4_2
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f201,plain,
    ( spl4_13
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f407,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)
    | ~ spl4_13 ),
    inference(resolution,[],[f203,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f203,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f201])).

fof(f834,plain,
    ( ~ spl4_1
    | spl4_40 ),
    inference(avatar_split_clause,[],[f833,f444,f94])).

fof(f833,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f832,f63])).

fof(f832,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f742,f186])).

fof(f742,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f330,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f754,plain,
    ( spl4_61
    | spl4_40 ),
    inference(avatar_split_clause,[],[f745,f444,f690])).

fof(f745,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f330,f68])).

fof(f449,plain,
    ( spl4_20
    | spl4_1 ),
    inference(avatar_split_clause,[],[f448,f94,f247])).

fof(f448,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f323,f63])).

fof(f323,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f186,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f354,plain,
    ( spl4_22
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl4_22
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f347,f273])).

fof(f273,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl4_22
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f347,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_24 ),
    inference(resolution,[],[f281,f89])).

fof(f89,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f281,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl4_24
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f329,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl4_24 ),
    inference(subsumption_resolution,[],[f327,f63])).

fof(f327,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_24 ),
    inference(subsumption_resolution,[],[f319,f282])).

fof(f282,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f280])).

fof(f319,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f186,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f310,plain,
    ( ~ spl4_22
    | spl4_30 ),
    inference(avatar_split_clause,[],[f304,f307,f271])).

fof(f304,plain,
    ( v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f190,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f190,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f189,f62])).

fof(f189,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f179,f63])).

fof(f179,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f64,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f278,plain,
    ( ~ spl4_22
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f264,f275,f271])).

fof(f264,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(resolution,[],[f184,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f184,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f183,f62])).

fof(f183,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f176,f63])).

fof(f176,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f64,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f204,plain,
    ( spl4_4
    | spl4_13 ),
    inference(avatar_split_clause,[],[f182,f201,f114])).

fof(f182,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f64,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f199,plain,
    ( ~ spl4_12
    | spl4_11 ),
    inference(avatar_split_clause,[],[f194,f166,f196])).

fof(f194,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1) ),
    inference(subsumption_resolution,[],[f181,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f181,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f64,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f193,plain,
    ( ~ spl4_2
    | ~ spl4_10
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f192,f110,f139,f98])).

fof(f139,plain,
    ( spl4_10
  <=> v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f110,plain,
    ( spl4_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f192,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f191,f62])).

fof(f191,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f180,f111])).

fof(f111,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f180,plain,
    ( ~ v7_struct_0(sK0)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f64,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f169,plain,
    ( spl4_10
    | ~ spl4_11
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f161,f110,f166,f139])).

fof(f161,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v7_struct_0(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f111,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f160,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f158,f63])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_3 ),
    inference(resolution,[],[f112,f89])).

fof(f112,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f117,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f103,f114,f110])).

fof(f103,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f62,f86])).

fof(f102,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f65,f98,f94])).

fof(f65,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f66,f98,f94])).

fof(f66,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (21389)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.43  % (21389)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f921,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f101,f102,f117,f160,f169,f193,f199,f204,f278,f310,f329,f354,f449,f754,f834,f838,f855,f890,f920])).
% 0.20/0.43  fof(f920,plain,(
% 0.20/0.43    spl4_11 | ~spl4_30 | ~spl4_61),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f919])).
% 0.20/0.43  fof(f919,plain,(
% 0.20/0.43    $false | (spl4_11 | ~spl4_30 | ~spl4_61)),
% 0.20/0.43    inference(subsumption_resolution,[],[f756,f168])).
% 0.20/0.43  fof(f168,plain,(
% 0.20/0.43    ~v1_zfmisc_1(u1_struct_0(sK0)) | spl4_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f166])).
% 0.20/0.43  fof(f166,plain,(
% 0.20/0.43    spl4_11 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.43  fof(f756,plain,(
% 0.20/0.43    v1_zfmisc_1(u1_struct_0(sK0)) | (~spl4_30 | ~spl4_61)),
% 0.20/0.43    inference(backward_demodulation,[],[f309,f692])).
% 0.20/0.43  fof(f692,plain,(
% 0.20/0.43    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_61),
% 0.20/0.43    inference(avatar_component_clause,[],[f690])).
% 0.20/0.43  fof(f690,plain,(
% 0.20/0.43    spl4_61 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.20/0.43  fof(f309,plain,(
% 0.20/0.43    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl4_30),
% 0.20/0.43    inference(avatar_component_clause,[],[f307])).
% 0.20/0.43  fof(f307,plain,(
% 0.20/0.43    spl4_30 <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.43  fof(f890,plain,(
% 0.20/0.43    spl4_1 | ~spl4_40 | ~spl4_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f889,f247,f444,f94])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    spl4_1 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f444,plain,(
% 0.20/0.43    spl4_40 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.20/0.43  fof(f247,plain,(
% 0.20/0.43    spl4_20 <=> sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.43  fof(f889,plain,(
% 0.20/0.43    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_20),
% 0.20/0.43    inference(subsumption_resolution,[],[f888,f63])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    l1_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,X1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,X1),sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,negated_conjecture,(
% 0.20/0.43    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.43    inference(negated_conjecture,[],[f17])).
% 0.20/0.43  fof(f17,conjecture,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.20/0.43  fof(f888,plain,(
% 0.20/0.43    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl4_20),
% 0.20/0.43    inference(subsumption_resolution,[],[f683,f186])).
% 0.20/0.43  fof(f186,plain,(
% 0.20/0.43    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f185,f62])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ~v2_struct_0(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f52])).
% 0.20/0.43  fof(f185,plain,(
% 0.20/0.43    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | v2_struct_0(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f177,f63])).
% 0.20/0.43  fof(f177,plain,(
% 0.20/0.43    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f64,f83])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.43  fof(f14,axiom,(
% 0.20/0.43    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f52])).
% 0.20/0.43  fof(f683,plain,(
% 0.20/0.43    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~spl4_20),
% 0.20/0.43    inference(superposition,[],[f75,f249])).
% 0.20/0.43  fof(f249,plain,(
% 0.20/0.43    sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f247])).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f57])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f55,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(rectify,[],[f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.20/0.43  fof(f855,plain,(
% 0.20/0.43    ~spl4_11 | ~spl4_40 | spl4_4 | spl4_23),
% 0.20/0.43    inference(avatar_split_clause,[],[f854,f275,f114,f444,f166])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    spl4_4 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.43  fof(f275,plain,(
% 0.20/0.43    spl4_23 <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.43  fof(f854,plain,(
% 0.20/0.43    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0)) | (spl4_4 | spl4_23)),
% 0.20/0.43    inference(subsumption_resolution,[],[f751,f116])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f114])).
% 0.20/0.43  fof(f751,plain,(
% 0.20/0.43    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl4_23),
% 0.20/0.43    inference(subsumption_resolution,[],[f744,f277])).
% 0.20/0.43  fof(f277,plain,(
% 0.20/0.43    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | spl4_23),
% 0.20/0.43    inference(avatar_component_clause,[],[f275])).
% 0.20/0.43  fof(f744,plain,(
% 0.20/0.43    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.43    inference(resolution,[],[f330,f69])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.20/0.43  fof(f330,plain,(
% 0.20/0.43    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f320,f63])).
% 0.20/0.43  fof(f320,plain,(
% 0.20/0.43    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.43    inference(resolution,[],[f186,f84])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f38])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.43  fof(f838,plain,(
% 0.20/0.43    spl4_12 | spl4_2 | ~spl4_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f407,f201,f98,f196])).
% 0.20/0.43  fof(f196,plain,(
% 0.20/0.43    spl4_12 <=> u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    spl4_2 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.43  fof(f201,plain,(
% 0.20/0.43    spl4_13 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.43  fof(f407,plain,(
% 0.20/0.43    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = k6_domain_1(u1_struct_0(sK0),sK1) | ~spl4_13),
% 0.20/0.43    inference(resolution,[],[f203,f68])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(nnf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.43  fof(f203,plain,(
% 0.20/0.43    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f201])).
% 0.20/0.43  fof(f834,plain,(
% 0.20/0.43    ~spl4_1 | spl4_40),
% 0.20/0.43    inference(avatar_split_clause,[],[f833,f444,f94])).
% 0.20/0.43  fof(f833,plain,(
% 0.20/0.43    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f832,f63])).
% 0.20/0.43  fof(f832,plain,(
% 0.20/0.43    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f742,f186])).
% 0.20/0.43  fof(f742,plain,(
% 0.20/0.43    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.20/0.43    inference(resolution,[],[f330,f92])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(equality_resolution,[],[f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f57])).
% 0.20/0.43  fof(f754,plain,(
% 0.20/0.43    spl4_61 | spl4_40),
% 0.20/0.43    inference(avatar_split_clause,[],[f745,f444,f690])).
% 0.20/0.43  fof(f745,plain,(
% 0.20/0.43    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.43    inference(resolution,[],[f330,f68])).
% 0.20/0.43  fof(f449,plain,(
% 0.20/0.43    spl4_20 | spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f448,f94,f247])).
% 0.20/0.43  fof(f448,plain,(
% 0.20/0.43    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.43    inference(subsumption_resolution,[],[f323,f63])).
% 0.20/0.43  fof(f323,plain,(
% 0.20/0.43    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | sK2(sK0,k1_tex_2(sK0,sK1)) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.20/0.43    inference(resolution,[],[f186,f74])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f57])).
% 0.20/0.43  fof(f354,plain,(
% 0.20/0.43    spl4_22 | ~spl4_24),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f353])).
% 0.20/0.43  fof(f353,plain,(
% 0.20/0.43    $false | (spl4_22 | ~spl4_24)),
% 0.20/0.43    inference(subsumption_resolution,[],[f347,f273])).
% 0.20/0.43  fof(f273,plain,(
% 0.20/0.43    ~l1_struct_0(k1_tex_2(sK0,sK1)) | spl4_22),
% 0.20/0.43    inference(avatar_component_clause,[],[f271])).
% 0.20/0.43  fof(f271,plain,(
% 0.20/0.43    spl4_22 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.43  fof(f347,plain,(
% 0.20/0.43    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_24),
% 0.20/0.43    inference(resolution,[],[f281,f89])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.43  fof(f281,plain,(
% 0.20/0.43    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl4_24),
% 0.20/0.43    inference(avatar_component_clause,[],[f280])).
% 0.20/0.43  fof(f280,plain,(
% 0.20/0.43    spl4_24 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.43  fof(f329,plain,(
% 0.20/0.43    spl4_24),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f328])).
% 0.20/0.43  fof(f328,plain,(
% 0.20/0.43    $false | spl4_24),
% 0.20/0.43    inference(subsumption_resolution,[],[f327,f63])).
% 0.20/0.43  fof(f327,plain,(
% 0.20/0.43    ~l1_pre_topc(sK0) | spl4_24),
% 0.20/0.43    inference(subsumption_resolution,[],[f319,f282])).
% 0.20/0.43  fof(f282,plain,(
% 0.20/0.43    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl4_24),
% 0.20/0.43    inference(avatar_component_clause,[],[f280])).
% 0.20/0.43  fof(f319,plain,(
% 0.20/0.43    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 0.20/0.43    inference(resolution,[],[f186,f88])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.43  fof(f310,plain,(
% 0.20/0.43    ~spl4_22 | spl4_30),
% 0.20/0.43    inference(avatar_split_clause,[],[f304,f307,f271])).
% 0.20/0.43  fof(f304,plain,(
% 0.20/0.43    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.43    inference(resolution,[],[f190,f85])).
% 0.20/0.43  fof(f85,plain,(
% 0.20/0.43    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.20/0.43  fof(f190,plain,(
% 0.20/0.43    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.43    inference(subsumption_resolution,[],[f189,f62])).
% 0.20/0.43  fof(f189,plain,(
% 0.20/0.43    v7_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f179,f63])).
% 0.20/0.43  fof(f179,plain,(
% 0.20/0.43    v7_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f64,f81])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.43    inference(pure_predicate_removal,[],[f15])).
% 0.20/0.43  fof(f15,axiom,(
% 0.20/0.43    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.20/0.43  fof(f278,plain,(
% 0.20/0.43    ~spl4_22 | ~spl4_23),
% 0.20/0.43    inference(avatar_split_clause,[],[f264,f275,f271])).
% 0.20/0.43  fof(f264,plain,(
% 0.20/0.43    ~v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.43    inference(resolution,[],[f184,f86])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.43  fof(f184,plain,(
% 0.20/0.43    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.20/0.43    inference(subsumption_resolution,[],[f183,f62])).
% 0.20/0.43  fof(f183,plain,(
% 0.20/0.43    ~v2_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f176,f63])).
% 0.20/0.43  fof(f176,plain,(
% 0.20/0.43    ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f64,f82])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f37])).
% 0.20/0.43  fof(f204,plain,(
% 0.20/0.43    spl4_4 | spl4_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f182,f201,f114])).
% 0.20/0.43  fof(f182,plain,(
% 0.20/0.43    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.43    inference(resolution,[],[f64,f76])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.43    inference(flattening,[],[f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.43  fof(f199,plain,(
% 0.20/0.43    ~spl4_12 | spl4_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f194,f166,f196])).
% 0.20/0.43  fof(f194,plain,(
% 0.20/0.43    v1_zfmisc_1(u1_struct_0(sK0)) | u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f181,f90])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.20/0.43  fof(f181,plain,(
% 0.20/0.43    v1_zfmisc_1(u1_struct_0(sK0)) | u1_struct_0(sK0) != k6_domain_1(u1_struct_0(sK0),sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.43    inference(resolution,[],[f64,f79])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f61])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f59,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.43    inference(rectify,[],[f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 0.20/0.43    inference(nnf_transformation,[],[f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.43  fof(f193,plain,(
% 0.20/0.43    ~spl4_2 | ~spl4_10 | ~spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f192,f110,f139,f98])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    spl4_10 <=> v7_struct_0(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.43  fof(f110,plain,(
% 0.20/0.43    spl4_3 <=> l1_struct_0(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.43  fof(f192,plain,(
% 0.20/0.43    ~v7_struct_0(sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_3),
% 0.20/0.43    inference(subsumption_resolution,[],[f191,f62])).
% 0.20/0.43  fof(f191,plain,(
% 0.20/0.43    ~v7_struct_0(sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl4_3),
% 0.20/0.43    inference(subsumption_resolution,[],[f180,f111])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    l1_struct_0(sK0) | ~spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f110])).
% 0.20/0.43  fof(f180,plain,(
% 0.20/0.43    ~v7_struct_0(sK0) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f64,f70])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,axiom,(
% 0.20/0.43    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 0.20/0.43  fof(f169,plain,(
% 0.20/0.43    spl4_10 | ~spl4_11 | ~spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f161,f110,f166,f139])).
% 0.20/0.43  fof(f161,plain,(
% 0.20/0.43    ~v1_zfmisc_1(u1_struct_0(sK0)) | v7_struct_0(sK0) | ~spl4_3),
% 0.20/0.43    inference(resolution,[],[f111,f87])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.20/0.43  fof(f160,plain,(
% 0.20/0.43    spl4_3),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f159])).
% 0.20/0.43  fof(f159,plain,(
% 0.20/0.43    $false | spl4_3),
% 0.20/0.43    inference(subsumption_resolution,[],[f158,f63])).
% 0.20/0.43  fof(f158,plain,(
% 0.20/0.43    ~l1_pre_topc(sK0) | spl4_3),
% 0.20/0.43    inference(resolution,[],[f112,f89])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    ~l1_struct_0(sK0) | spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f110])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    ~spl4_3 | ~spl4_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f103,f114,f110])).
% 0.20/0.43  fof(f103,plain,(
% 0.20/0.43    ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f62,f86])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    spl4_1 | spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f65,f98,f94])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f52])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    ~spl4_1 | ~spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f66,f98,f94])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f52])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (21389)------------------------------
% 0.20/0.43  % (21389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (21389)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (21389)Memory used [KB]: 6524
% 0.20/0.43  % (21389)Time elapsed: 0.017 s
% 0.20/0.43  % (21389)------------------------------
% 0.20/0.43  % (21389)------------------------------
% 0.20/0.44  % (21369)Success in time 0.081 s
%------------------------------------------------------------------------------
