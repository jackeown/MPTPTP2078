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
% DateTime   : Thu Dec  3 13:22:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 475 expanded)
%              Number of leaves         :   42 ( 189 expanded)
%              Depth                    :   13
%              Number of atoms          :  895 (2414 expanded)
%              Number of equality atoms :   28 (  85 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f504,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f100,f105,f110,f125,f130,f139,f141,f152,f176,f183,f200,f213,f231,f292,f306,f315,f337,f341,f360,f372,f385,f400,f428,f480,f487,f498,f503])).

fof(f503,plain,
    ( u1_struct_0(sK0) != sK1
    | m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f498,plain,
    ( spl6_12
    | ~ spl6_20
    | ~ spl6_45 ),
    inference(avatar_contradiction_clause,[],[f492])).

fof(f492,plain,
    ( $false
    | spl6_12
    | ~ spl6_20
    | ~ spl6_45 ),
    inference(unit_resulting_resolution,[],[f138,f230,f486,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f486,plain,
    ( r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,k3_yellow_0(sK0)))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl6_45
  <=> r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,k3_yellow_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f230,plain,
    ( m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(sK1))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl6_20
  <=> m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f138,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_12
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f487,plain,
    ( spl6_45
    | ~ spl6_16
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f481,f478,f173,f484])).

fof(f173,plain,
    ( spl6_16
  <=> m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f478,plain,
    ( spl6_44
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f481,plain,
    ( r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,k3_yellow_0(sK0)))
    | ~ spl6_16
    | ~ spl6_44 ),
    inference(resolution,[],[f479,f175])).

fof(f175,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f173])).

fof(f479,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) )
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f478])).

fof(f480,plain,
    ( spl6_44
    | ~ spl6_13
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f418,f339,f149,f478])).

fof(f149,plain,
    ( spl6_13
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f339,plain,
    ( spl6_34
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f418,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) )
    | ~ spl6_13
    | ~ spl6_34 ),
    inference(backward_demodulation,[],[f340,f151])).

fof(f151,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f340,plain,
    ( ! [X0] :
        ( r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f339])).

fof(f428,plain,
    ( ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f406,f168])).

fof(f168,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f71,f145])).

fof(f145,plain,(
    ! [X0] : sK4(X0) = X0 ),
    inference(subsumption_resolution,[],[f143,f71])).

fof(f143,plain,(
    ! [X0] :
      ( sK4(X0) = X0
      | v1_subset_1(sK4(X0),X0) ) ),
    inference(resolution,[],[f73,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK4(X0),X0)
      & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f71,plain,(
    ! [X0] : ~ v1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f406,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f134,f151])).

fof(f134,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_11
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f400,plain,
    ( ~ spl6_10
    | spl6_13
    | ~ spl6_29
    | ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl6_10
    | spl6_13
    | ~ spl6_29
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f398,f167])).

fof(f167,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f70,f145])).

fof(f398,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10
    | spl6_13
    | ~ spl6_29
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f397,f129])).

fof(f129,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f397,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_13
    | ~ spl6_29
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f396,f305])).

fof(f305,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl6_29
  <=> r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f396,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_13
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f394,f150])).

fof(f150,plain,
    ( u1_struct_0(sK0) != sK1
    | spl6_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f394,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_38 ),
    inference(resolution,[],[f384,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X2)
      | X1 = X2
      | ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK5(X0,X1,X2),X2)
              | ~ r2_hidden(sK5(X0,X1,X2),X1) )
            & ( r2_hidden(sK5(X0,X1,X2),X2)
              | r2_hidden(sK5(X0,X1,X2),X1) )
            & m1_subset_1(sK5(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK5(X0,X1,X2),X2)
          | ~ r2_hidden(sK5(X0,X1,X2),X1) )
        & ( r2_hidden(sK5(X0,X1,X2),X2)
          | r2_hidden(sK5(X0,X1,X2),X1) )
        & m1_subset_1(sK5(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f384,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f382])).

fof(f382,plain,
    ( spl6_38
  <=> r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f385,plain,
    ( spl6_38
    | ~ spl6_27
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f377,f370,f289,f382])).

fof(f289,plain,
    ( spl6_27
  <=> m1_subset_1(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f370,plain,
    ( spl6_37
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f377,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | ~ spl6_27
    | ~ spl6_37 ),
    inference(resolution,[],[f371,f291])).

fof(f291,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f289])).

fof(f371,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f370])).

fof(f372,plain,
    ( spl6_37
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f368,f358,f335,f127,f122,f107,f370])).

fof(f107,plain,
    ( spl6_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f122,plain,
    ( spl6_9
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f335,plain,
    ( spl6_33
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(X0,k3_yellow_0(sK0),X1)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f358,plain,
    ( spl6_36
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k3_yellow_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f368,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_33
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f356,f359])).

fof(f359,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f358])).

fof(f356,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k3_yellow_0(sK0),X0) )
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f355,f109])).

fof(f109,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f355,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f354,f124])).

fof(f124,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f354,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(sK1,sK0)
        | ~ r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(resolution,[],[f336,f129])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ r1_orders_2(X0,k3_yellow_0(sK0),X1)
        | ~ l1_orders_2(X0) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f335])).

fof(f360,plain,
    ( spl6_36
    | spl6_1
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f353,f339,f210,f107,f82,f358])).

fof(f82,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f210,plain,
    ( spl6_19
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k3_yellow_0(sK0),X0) )
    | spl6_1
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f352,f84])).

fof(f84,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | v2_struct_0(sK0) )
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f351,f109])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_19
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f350,f212])).

fof(f212,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f210])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_34 ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,k3_yellow_0(sK0),X0)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_34 ),
    inference(resolution,[],[f340,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).

fof(f341,plain,
    ( spl6_34
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f332,f313,f210,f107,f102,f97,f82,f339])).

fof(f97,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f102,plain,
    ( spl6_5
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f313,plain,
    ( spl6_30
  <=> ! [X1,X0] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X0,k5_waybel_0(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f331,f84])).

fof(f331,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f330,f99])).

fof(f99,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f330,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0))
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f329,f104])).

fof(f104,plain,
    ( v1_yellow_0(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0))
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_6
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f328,f109])).

fof(f328,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0))
        | ~ l1_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_19
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f327,f212])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0))
        | ~ l1_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_30 ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_30 ),
    inference(resolution,[],[f314,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f314,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X0,k5_waybel_0(sK0,X1)) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f313])).

fof(f337,plain,
    ( spl6_33
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f232,f136,f335])).

fof(f232,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(X0,k3_yellow_0(sK0),X1)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v13_waybel_0(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f137,f223])).

fof(f223,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | r2_hidden(X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f61,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f61,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK2(X0,X1),X3)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f137,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f315,plain,
    ( spl6_30
    | spl6_1
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f208,f107,f82,f313])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X0,k5_waybel_0(sK0,X1)) )
    | spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f207,f84])).

fof(f207,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X0,k5_waybel_0(sK0,X1))
        | v2_struct_0(sK0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f69,f109])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X2,k5_waybel_0(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f306,plain,
    ( spl6_29
    | ~ spl6_10
    | spl6_13 ),
    inference(avatar_split_clause,[],[f297,f149,f127,f303])).

fof(f297,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_10
    | spl6_13 ),
    inference(subsumption_resolution,[],[f296,f150])).

fof(f296,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1
    | ~ spl6_10 ),
    inference(resolution,[],[f222,f129])).

fof(f222,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK5(X0,X0,X1),X0)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f221,f74])).

fof(f221,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X0,X1),X1)
      | r2_hidden(sK5(X0,X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1 ) ),
    inference(resolution,[],[f76,f167])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f292,plain,
    ( spl6_27
    | ~ spl6_10
    | spl6_13 ),
    inference(avatar_split_clause,[],[f287,f149,f127,f289])).

fof(f287,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl6_10
    | spl6_13 ),
    inference(subsumption_resolution,[],[f286,f150])).

fof(f286,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = sK1
    | ~ spl6_10 ),
    inference(resolution,[],[f196,f129])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK5(X0,X0,X1),X0)
      | X0 = X1 ) ),
    inference(resolution,[],[f75,f167])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK5(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f231,plain,
    ( spl6_20
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f224,f198,f173,f228])).

fof(f198,plain,
    ( spl6_18
  <=> ! [X0] :
        ( m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f224,plain,
    ( m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(sK1))
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(resolution,[],[f199,f175])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(sK1)) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f198])).

fof(f213,plain,
    ( spl6_19
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f205,f181,f127,f210])).

fof(f181,plain,
    ( spl6_17
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(k3_yellow_0(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f205,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(resolution,[],[f182,f129])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(k3_yellow_0(sK0),X0) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f181])).

fof(f200,plain,
    ( spl6_18
    | spl6_1
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f191,f149,f107,f82,f198])).

fof(f191,plain,
    ( ! [X0] :
        ( m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(sK1))
        | ~ m1_subset_1(X0,sK1) )
    | spl6_1
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f190,f151])).

fof(f190,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f189,f151])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl6_1
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f188,f84])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f78,f109])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).

fof(f183,plain,
    ( spl6_17
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f177,f136,f181])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | m1_subset_1(k3_yellow_0(sK0),X0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f137,f79])).

fof(f176,plain,
    ( spl6_16
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f166,f149,f107,f173])).

fof(f166,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f165,f109])).

fof(f165,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl6_13 ),
    inference(superposition,[],[f60,f151])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f152,plain,
    ( spl6_13
    | ~ spl6_10
    | spl6_11 ),
    inference(avatar_split_clause,[],[f144,f132,f127,f149])).

fof(f144,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl6_10
    | spl6_11 ),
    inference(subsumption_resolution,[],[f142,f133])).

fof(f133,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f142,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(resolution,[],[f73,f129])).

fof(f141,plain,
    ( ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f140,f136,f132])).

fof(f140,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_12 ),
    inference(subsumption_resolution,[],[f59,f138])).

fof(f59,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
    & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | v1_subset_1(sK1,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & v2_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
          & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
            | v1_subset_1(X1,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & v2_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK0),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
        & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
          | v1_subset_1(X1,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & v2_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & v2_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f139,plain,
    ( spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f58,f136,f132])).

fof(f58,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f130,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f57,f127])).

fof(f57,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f125,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f56,f122])).

fof(f56,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f110,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f53,f107])).

fof(f53,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f105,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f52,f102])).

fof(f52,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f51,f97])).

fof(f51,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f48,f82])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (27028)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (27028)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (27029)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (27036)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (27044)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.50  % (27037)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f504,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f85,f100,f105,f110,f125,f130,f139,f141,f152,f176,f183,f200,f213,f231,f292,f306,f315,f337,f341,f360,f372,f385,f400,f428,f480,f487,f498,f503])).
% 0.21/0.50  fof(f503,plain,(
% 0.21/0.50    u1_struct_0(sK0) != sK1 | m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f498,plain,(
% 0.21/0.50    spl6_12 | ~spl6_20 | ~spl6_45),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f492])).
% 0.21/0.50  fof(f492,plain,(
% 0.21/0.50    $false | (spl6_12 | ~spl6_20 | ~spl6_45)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f138,f230,f486,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.50  fof(f486,plain,(
% 0.21/0.50    r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,k3_yellow_0(sK0))) | ~spl6_45),
% 0.21/0.50    inference(avatar_component_clause,[],[f484])).
% 0.21/0.50  fof(f484,plain,(
% 0.21/0.50    spl6_45 <=> r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,k3_yellow_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(sK1)) | ~spl6_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f228])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    spl6_20 <=> m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl6_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl6_12 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.50  fof(f487,plain,(
% 0.21/0.50    spl6_45 | ~spl6_16 | ~spl6_44),
% 0.21/0.50    inference(avatar_split_clause,[],[f481,f478,f173,f484])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    spl6_16 <=> m1_subset_1(k3_yellow_0(sK0),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.50  fof(f478,plain,(
% 0.21/0.50    spl6_44 <=> ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.50  fof(f481,plain,(
% 0.21/0.50    r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,k3_yellow_0(sK0))) | (~spl6_16 | ~spl6_44)),
% 0.21/0.50    inference(resolution,[],[f479,f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    m1_subset_1(k3_yellow_0(sK0),sK1) | ~spl6_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f173])).
% 0.21/0.50  fof(f479,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0))) ) | ~spl6_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f478])).
% 0.21/0.50  fof(f480,plain,(
% 0.21/0.50    spl6_44 | ~spl6_13 | ~spl6_34),
% 0.21/0.50    inference(avatar_split_clause,[],[f418,f339,f149,f478])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    spl6_13 <=> u1_struct_0(sK0) = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    spl6_34 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.50  fof(f418,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0))) ) | (~spl6_13 | ~spl6_34)),
% 0.21/0.50    inference(backward_demodulation,[],[f340,f151])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    u1_struct_0(sK0) = sK1 | ~spl6_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f149])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_34),
% 0.21/0.50    inference(avatar_component_clause,[],[f339])).
% 0.21/0.50  fof(f428,plain,(
% 0.21/0.50    ~spl6_11 | ~spl6_13),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f427])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    $false | (~spl6_11 | ~spl6_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f406,f168])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f71,f145])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ( ! [X0] : (sK4(X0) = X0) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f143,f71])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ( ! [X0] : (sK4(X0) = X0 | v1_subset_1(sK4(X0),X0)) )),
% 0.21/0.50    inference(resolution,[],[f73,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0] : (~v1_subset_1(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f3,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_subset_1(sK4(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f406,plain,(
% 0.21/0.50    v1_subset_1(sK1,sK1) | (~spl6_11 | ~spl6_13)),
% 0.21/0.50    inference(backward_demodulation,[],[f134,f151])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    spl6_11 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.50  fof(f400,plain,(
% 0.21/0.50    ~spl6_10 | spl6_13 | ~spl6_29 | ~spl6_38),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f399])).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    $false | (~spl6_10 | spl6_13 | ~spl6_29 | ~spl6_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f398,f167])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f70,f145])).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_10 | spl6_13 | ~spl6_29 | ~spl6_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f397,f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl6_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.50  fof(f397,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_13 | ~spl6_29 | ~spl6_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f396,f305])).
% 0.21/0.50  fof(f305,plain,(
% 0.21/0.50    r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl6_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f303])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    spl6_29 <=> r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.50  fof(f396,plain,(
% 0.21/0.50    ~r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_13 | ~spl6_38)),
% 0.21/0.50    inference(subsumption_resolution,[],[f394,f150])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    u1_struct_0(sK0) != sK1 | spl6_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f149])).
% 0.21/0.50  fof(f394,plain,(
% 0.21/0.50    u1_struct_0(sK0) = sK1 | ~r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_38),
% 0.21/0.50    inference(resolution,[],[f384,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X2) | X1 = X2 | ~r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1)) & (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1)) & m1_subset_1(sK5(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f45,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK5(X0,X1,X2),X2) | ~r2_hidden(sK5(X0,X1,X2),X1)) & (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1)) & m1_subset_1(sK5(X0,X1,X2),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | ~spl6_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f382])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    spl6_38 <=> r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    spl6_38 | ~spl6_27 | ~spl6_37),
% 0.21/0.50    inference(avatar_split_clause,[],[f377,f370,f289,f382])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    spl6_27 <=> m1_subset_1(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    spl6_37 <=> ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | (~spl6_27 | ~spl6_37)),
% 0.21/0.50    inference(resolution,[],[f371,f291])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    m1_subset_1(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl6_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f289])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | ~spl6_37),
% 0.21/0.50    inference(avatar_component_clause,[],[f370])).
% 0.21/0.50  fof(f372,plain,(
% 0.21/0.50    spl6_37 | ~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_33 | ~spl6_36),
% 0.21/0.50    inference(avatar_split_clause,[],[f368,f358,f335,f127,f122,f107,f370])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl6_6 <=> l1_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl6_9 <=> v13_waybel_0(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    spl6_33 <=> ! [X1,X0] : (~r1_orders_2(X0,k3_yellow_0(sK0),X1) | r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_waybel_0(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    spl6_36 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_33 | ~spl6_36)),
% 0.21/0.50    inference(subsumption_resolution,[],[f356,f359])).
% 0.21/0.50  fof(f359,plain,(
% 0.21/0.50    ( ! [X0] : (r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f358])).
% 0.21/0.50  fof(f356,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k3_yellow_0(sK0),X0)) ) | (~spl6_6 | ~spl6_9 | ~spl6_10 | ~spl6_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f355,f109])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    l1_orders_2(sK0) | ~spl6_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f107])).
% 0.21/0.50  fof(f355,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0)) ) | (~spl6_9 | ~spl6_10 | ~spl6_33)),
% 0.21/0.50    inference(subsumption_resolution,[],[f354,f124])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    v13_waybel_0(sK1,sK0) | ~spl6_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f122])).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v13_waybel_0(sK1,sK0) | ~r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0)) ) | (~spl6_10 | ~spl6_33)),
% 0.21/0.50    inference(resolution,[],[f336,f129])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_waybel_0(sK1,X0) | ~r1_orders_2(X0,k3_yellow_0(sK0),X1) | ~l1_orders_2(X0)) ) | ~spl6_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f335])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    spl6_36 | spl6_1 | ~spl6_6 | ~spl6_19 | ~spl6_34),
% 0.21/0.50    inference(avatar_split_clause,[],[f353,f339,f210,f107,f82,f358])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl6_1 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    spl6_19 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.50  fof(f353,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0)) ) | (spl6_1 | ~spl6_6 | ~spl6_19 | ~spl6_34)),
% 0.21/0.50    inference(subsumption_resolution,[],[f352,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ~v2_struct_0(sK0) | spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f352,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0) | v2_struct_0(sK0)) ) | (~spl6_6 | ~spl6_19 | ~spl6_34)),
% 0.21/0.50    inference(subsumption_resolution,[],[f351,f109])).
% 0.21/0.50  fof(f351,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_19 | ~spl6_34)),
% 0.21/0.50    inference(subsumption_resolution,[],[f350,f212])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl6_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f210])).
% 0.21/0.50  fof(f350,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_34),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f346])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,k3_yellow_0(sK0),X0) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_34),
% 0.21/0.50    inference(resolution,[],[f340,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_waybel_0(X0,X1)) | r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k5_waybel_0(X0,X1)) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_hidden(X2,k5_waybel_0(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k5_waybel_0(X0,X1)) <=> r1_orders_2(X0,X2,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_waybel_0)).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    spl6_34 | spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_19 | ~spl6_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f332,f313,f210,f107,f102,f97,f82,f339])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl6_4 <=> v5_orders_2(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl6_5 <=> v1_yellow_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    spl6_30 <=> ! [X1,X0] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X0,k5_waybel_0(sK0,X1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0))) ) | (spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_19 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f331,f84])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_19 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f330,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    v5_orders_2(sK0) | ~spl6_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f330,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_19 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f329,f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    v1_yellow_0(sK0) | ~spl6_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_6 | ~spl6_19 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f328,f109])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_19 | ~spl6_30)),
% 0.21/0.50    inference(subsumption_resolution,[],[f327,f212])).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_30),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f325])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),k5_waybel_0(sK0,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_30),
% 0.21/0.50    inference(resolution,[],[f314,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X0,k5_waybel_0(sK0,X1))) ) | ~spl6_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f313])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    spl6_33 | ~spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f232,f136,f335])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_orders_2(X0,k3_yellow_0(sK0),X1) | r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_waybel_0(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) ) | ~spl6_12),
% 0.21/0.50    inference(resolution,[],[f137,f223])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X4,X0,X5,X1] : (~r2_hidden(X4,X1) | ~r1_orders_2(X0,X4,X5) | r2_hidden(X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f61,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(rectify,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl6_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    spl6_30 | spl6_1 | ~spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f208,f107,f82,f313])).
% 0.21/0.50  fof(f208,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X0,k5_waybel_0(sK0,X1))) ) | (spl6_1 | ~spl6_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f207,f84])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X0,k5_waybel_0(sK0,X1)) | v2_struct_0(sK0)) ) | ~spl6_6),
% 0.21/0.50    inference(resolution,[],[f69,f109])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(X2,k5_waybel_0(X0,X1)) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    spl6_29 | ~spl6_10 | spl6_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f297,f149,f127,f303])).
% 0.21/0.50  fof(f297,plain,(
% 0.21/0.50    r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl6_10 | spl6_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f296,f150])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    r2_hidden(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1 | ~spl6_10),
% 0.21/0.50    inference(resolution,[],[f222,f129])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK5(X0,X0,X1),X0) | X0 = X1) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f221,f74])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK5(X0,X0,X1),X1) | r2_hidden(sK5(X0,X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1) )),
% 0.21/0.51    inference(resolution,[],[f76,f167])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    spl6_27 | ~spl6_10 | spl6_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f287,f149,f127,f289])).
% 0.21/0.51  fof(f287,plain,(
% 0.21/0.51    m1_subset_1(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | (~spl6_10 | spl6_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f286,f150])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    m1_subset_1(sK5(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = sK1 | ~spl6_10),
% 0.21/0.51    inference(resolution,[],[f196,f129])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK5(X0,X0,X1),X0) | X0 = X1) )),
% 0.21/0.51    inference(resolution,[],[f75,f167])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK5(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f47])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    spl6_20 | ~spl6_16 | ~spl6_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f224,f198,f173,f228])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    spl6_18 <=> ! [X0] : (m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    m1_subset_1(k5_waybel_0(sK0,k3_yellow_0(sK0)),k1_zfmisc_1(sK1)) | (~spl6_16 | ~spl6_18)),
% 0.21/0.51    inference(resolution,[],[f199,f175])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(sK1))) ) | ~spl6_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f198])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    spl6_19 | ~spl6_10 | ~spl6_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f205,f181,f127,f210])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    spl6_17 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | m1_subset_1(k3_yellow_0(sK0),X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | (~spl6_10 | ~spl6_17)),
% 0.21/0.51    inference(resolution,[],[f182,f129])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | m1_subset_1(k3_yellow_0(sK0),X0)) ) | ~spl6_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f181])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    spl6_18 | spl6_1 | ~spl6_6 | ~spl6_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f191,f149,f107,f82,f198])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(sK1)) | ~m1_subset_1(X0,sK1)) ) | (spl6_1 | ~spl6_6 | ~spl6_13)),
% 0.21/0.51    inference(forward_demodulation,[],[f190,f151])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_6 | ~spl6_13)),
% 0.21/0.51    inference(forward_demodulation,[],[f189,f151])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl6_1 | ~spl6_6)),
% 0.21/0.51    inference(subsumption_resolution,[],[f188,f84])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k5_waybel_0(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) ) | ~spl6_6),
% 0.21/0.51    inference(resolution,[],[f78,f109])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_waybel_0)).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    spl6_17 | ~spl6_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f177,f136,f181])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | m1_subset_1(k3_yellow_0(sK0),X0)) ) | ~spl6_12),
% 0.21/0.51    inference(resolution,[],[f137,f79])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    spl6_16 | ~spl6_6 | ~spl6_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f166,f149,f107,f173])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    m1_subset_1(k3_yellow_0(sK0),sK1) | (~spl6_6 | ~spl6_13)),
% 0.21/0.51    inference(subsumption_resolution,[],[f165,f109])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    m1_subset_1(k3_yellow_0(sK0),sK1) | ~l1_orders_2(sK0) | ~spl6_13),
% 0.21/0.51    inference(superposition,[],[f60,f151])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    spl6_13 | ~spl6_10 | spl6_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f144,f132,f127,f149])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    u1_struct_0(sK0) = sK1 | (~spl6_10 | spl6_11)),
% 0.21/0.51    inference(subsumption_resolution,[],[f142,f133])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl6_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f132])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_10),
% 0.21/0.51    inference(resolution,[],[f73,f129])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ~spl6_11 | spl6_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f140,f136,f132])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl6_12),
% 0.21/0.51    inference(subsumption_resolution,[],[f59,f138])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    spl6_11 | ~spl6_12),
% 0.21/0.51    inference(avatar_split_clause,[],[f58,f136,f132])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    spl6_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f57,f127])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f122])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    v13_waybel_0(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f53,f107])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    l1_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f102])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    v1_yellow_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f97])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v5_orders_2(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ~spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f82])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (27028)------------------------------
% 0.21/0.51  % (27028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27028)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (27028)Memory used [KB]: 6396
% 0.21/0.51  % (27028)Time elapsed: 0.088 s
% 0.21/0.51  % (27028)------------------------------
% 0.21/0.51  % (27028)------------------------------
% 0.21/0.51  % (27020)Success in time 0.141 s
%------------------------------------------------------------------------------
