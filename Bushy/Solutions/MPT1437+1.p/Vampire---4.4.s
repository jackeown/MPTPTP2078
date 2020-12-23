%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t32_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:08 EDT 2019

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 605 expanded)
%              Number of leaves         :   29 ( 215 expanded)
%              Depth                    :   16
%              Number of atoms          :  525 (4188 expanded)
%              Number of equality atoms :   55 ( 150 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6001,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f150,f170,f188,f190,f200,f204,f208,f210,f220,f233,f2499,f2518,f4257,f5518,f5756,f6000])).

fof(f6000,plain,
    ( spl11_8
    | ~ spl11_13
    | ~ spl11_15
    | spl11_2
    | ~ spl11_1099
    | ~ spl11_1050 ),
    inference(avatar_split_clause,[],[f5999,f5516,f5746,f148,f177,f174,f165])).

fof(f165,plain,
    ( spl11_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f174,plain,
    ( spl11_13
  <=> ~ v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f177,plain,
    ( spl11_15
  <=> ~ l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f148,plain,
    ( spl11_2
  <=> r3_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f5746,plain,
    ( spl11_1099
  <=> ~ r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1099])])).

fof(f5516,plain,
    ( spl11_1050
  <=> k4_tarski(sK1,sK2) = k4_tarski(sK4(k4_tarski(sK1,sK2),sK0),sK5(k4_tarski(sK1,sK2),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1050])])).

fof(f5999,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | r3_lattices(sK0,sK1,sK2)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1050 ),
    inference(forward_demodulation,[],[f5998,f152])).

fof(f152,plain,(
    k8_filter_1(sK0) = a_1_0_filter_1(sK0) ),
    inference(global_subsumption,[],[f93,f94,f151])).

fof(f151,plain,
    ( k8_filter_1(sK0) = a_1_0_filter_1(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f95,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = a_1_0_filter_1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k8_filter_1(X0) = a_1_0_filter_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t32_filter_1.p',d8_filter_1)).

fof(f95,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,
    ( ( ~ r3_lattices(sK0,sK1,sK2)
      | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) )
    & ( r3_lattices(sK0,sK1,sK2)
      | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f70,f73,f72,f71])).

fof(f71,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_lattices(X0,X1,X2)
                  | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
                & ( r3_lattices(X0,X1,X2)
                  | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(sK0,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X1,X2),k8_filter_1(sK0)) )
              & ( r3_lattices(sK0,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),X1,X2),k8_filter_1(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & ( r3_lattices(X0,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r3_lattices(X0,sK1,X2)
              | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),sK1,X2),k8_filter_1(X0)) )
            & ( r3_lattices(X0,sK1,X2)
              | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),sK1,X2),k8_filter_1(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r3_lattices(X0,X1,X2)
            | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
          & ( r3_lattices(X0,X1,X2)
            | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r3_lattices(X0,X1,sK2)
          | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,sK2),k8_filter_1(X0)) )
        & ( r3_lattices(X0,X1,sK2)
          | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,sK2),k8_filter_1(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & ( r3_lattices(X0,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_lattices(X0,X1,X2)
                | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & ( r3_lattices(X0,X1,X2)
                | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <~> r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <~> r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
                <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t32_filter_1.p',t32_filter_1)).

fof(f94,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f93,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f74])).

fof(f5998,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1050 ),
    inference(forward_demodulation,[],[f5997,f5725])).

fof(f5725,plain,
    ( sK1 = sK4(k4_tarski(sK1,sK2),sK0)
    | ~ spl11_1050 ),
    inference(equality_resolution,[],[f5708])).

fof(f5708,plain,
    ( ! [X0,X1] :
        ( k4_tarski(sK1,sK2) != k4_tarski(X0,X1)
        | sK4(k4_tarski(sK1,sK2),sK0) = X0 )
    | ~ spl11_1050 ),
    inference(superposition,[],[f128,f5517])).

fof(f5517,plain,
    ( k4_tarski(sK1,sK2) = k4_tarski(sK4(k4_tarski(sK1,sK2),sK0),sK5(k4_tarski(sK1,sK2),sK0))
    | ~ spl11_1050 ),
    inference(avatar_component_clause,[],[f5516])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3] :
      ( ( X1 = X3
        & X0 = X2 )
      | k4_tarski(X0,X1) != k4_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( k4_tarski(X0,X1) = k4_tarski(X2,X3)
     => ( X1 = X3
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t32_filter_1.p',t33_zfmisc_1)).

fof(f5997,plain,
    ( r3_lattices(sK0,sK4(k4_tarski(sK1,sK2),sK0),sK2)
    | ~ r2_hidden(k4_tarski(sK1,sK2),a_1_0_filter_1(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1050 ),
    inference(superposition,[],[f119,f5983])).

fof(f5983,plain,
    ( sK2 = sK5(k4_tarski(sK1,sK2),sK0)
    | ~ spl11_1050 ),
    inference(equality_resolution,[],[f5710])).

fof(f5710,plain,
    ( ! [X4,X5] :
        ( k4_tarski(sK1,sK2) != k4_tarski(X4,X5)
        | sK5(k4_tarski(sK1,sK2),sK0) = X5 )
    | ~ spl11_1050 ),
    inference(superposition,[],[f129,f5517])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != k4_tarski(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r3_lattices(X1,sK4(X0,X1),sK5(X0,X1))
      | ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,a_1_0_filter_1(X1))
          | ! [X2,X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
        & ( ( r3_lattices(X1,sK4(X0,X1),sK5(X0,X1))
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK4(X0,X1),sK5(X0,X1)) = X0
            & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
            & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f78,f79])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ? [X4,X5] :
          ( r3_lattices(X1,X4,X5)
          & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X4,X5) = X0
          & m1_subset_1(X5,u1_struct_0(X1))
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,sK4(X0,X1),sK5(X0,X1))
        & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK4(X0,X1),sK5(X0,X1)) = X0
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,a_1_0_filter_1(X1))
          | ! [X2,X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
        & ( ? [X4,X5] :
              ( r3_lattices(X1,X4,X5)
              & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X4,X5) = X0
              & m1_subset_1(X5,u1_struct_0(X1))
              & m1_subset_1(X4,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,a_1_0_filter_1(X1))
          | ! [X2,X3] :
              ( ~ r3_lattices(X1,X2,X3)
              | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X1))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) ) )
        & ( ? [X2,X3] :
              ( r3_lattices(X1,X2,X3)
              & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
              & m1_subset_1(X3,u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_1_0_filter_1(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_1_0_filter_1(X1))
      <=> ? [X2,X3] :
            ( r3_lattices(X1,X2,X3)
            & k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X1))
            & m1_subset_1(X2,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t32_filter_1.p',fraenkel_a_1_0_filter_1)).

fof(f5756,plain,
    ( ~ spl11_0
    | ~ spl11_44
    | spl11_1099 ),
    inference(avatar_contradiction_clause,[],[f5754])).

fof(f5754,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_44
    | ~ spl11_1099 ),
    inference(subsumption_resolution,[],[f339,f5747])).

fof(f5747,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | ~ spl11_1099 ),
    inference(avatar_component_clause,[],[f5746])).

fof(f339,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k8_filter_1(sK0))
    | ~ spl11_0
    | ~ spl11_44 ),
    inference(backward_demodulation,[],[f292,f146])).

fof(f146,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0))
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl11_0
  <=> r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f292,plain,
    ( k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k4_tarski(sK1,sK2)
    | ~ spl11_44 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl11_44
  <=> k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k4_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f5518,plain,
    ( spl11_4
    | spl11_1050
    | ~ spl11_0
    | ~ spl11_44
    | ~ spl11_98 ),
    inference(avatar_split_clause,[],[f5514,f460,f291,f145,f5516,f155])).

fof(f155,plain,
    ( spl11_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f460,plain,
    ( spl11_98
  <=> ! [X1,X0] :
        ( k1_domain_1(X0,u1_struct_0(sK0),X1,sK5(k4_tarski(sK1,sK2),sK0)) = k4_tarski(X1,sK5(k4_tarski(sK1,sK2),sK0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_98])])).

fof(f5514,plain,
    ( k4_tarski(sK1,sK2) = k4_tarski(sK4(k4_tarski(sK1,sK2),sK0),sK5(k4_tarski(sK1,sK2),sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_0
    | ~ spl11_44
    | ~ spl11_98 ),
    inference(forward_demodulation,[],[f5471,f418])).

fof(f418,plain,
    ( k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(k4_tarski(sK1,sK2),sK0),sK5(k4_tarski(sK1,sK2),sK0)) = k4_tarski(sK1,sK2)
    | ~ spl11_0
    | ~ spl11_44 ),
    inference(resolution,[],[f218,f339])).

fof(f218,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k8_filter_1(sK0))
      | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(X2,sK0),sK5(X2,sK0)) = X2 ) ),
    inference(global_subsumption,[],[f94,f95,f93,f215])).

fof(f215,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k8_filter_1(sK0))
      | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(X2,sK0),sK5(X2,sK0)) = X2
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f118,f152])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),sK4(X0,X1),sK5(X0,X1)) = X0
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f5471,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK4(k4_tarski(sK1,sK2),sK0),sK5(k4_tarski(sK1,sK2),sK0)) = k4_tarski(sK4(k4_tarski(sK1,sK2),sK0),sK5(k4_tarski(sK1,sK2),sK0))
    | ~ spl11_0
    | ~ spl11_44
    | ~ spl11_98 ),
    inference(resolution,[],[f461,f347])).

fof(f347,plain,
    ( m1_subset_1(sK4(k4_tarski(sK1,sK2),sK0),u1_struct_0(sK0))
    | ~ spl11_0
    | ~ spl11_44 ),
    inference(resolution,[],[f339,f216])).

fof(f216,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k8_filter_1(sK0))
      | m1_subset_1(sK4(X0,sK0),u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f94,f95,f93,f213])).

fof(f213,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k8_filter_1(sK0))
      | m1_subset_1(sK4(X0,sK0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f116,f152])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | m1_subset_1(sK4(X0,X1),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f461,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0)
        | k1_domain_1(X0,u1_struct_0(sK0),X1,sK5(k4_tarski(sK1,sK2),sK0)) = k4_tarski(X1,sK5(k4_tarski(sK1,sK2),sK0)) )
    | ~ spl11_98 ),
    inference(avatar_component_clause,[],[f460])).

fof(f4257,plain,
    ( spl11_4
    | spl11_98
    | ~ spl11_0
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f4240,f291,f145,f460,f155])).

fof(f4240,plain,
    ( ! [X0,X1] :
        ( k1_domain_1(X0,u1_struct_0(sK0),X1,sK5(k4_tarski(sK1,sK2),sK0)) = k4_tarski(X1,sK5(k4_tarski(sK1,sK2),sK0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(X0) )
    | ~ spl11_0
    | ~ spl11_44 ),
    inference(resolution,[],[f346,f130])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,X1)
      | k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t32_filter_1.p',redefinition_k1_domain_1)).

fof(f346,plain,
    ( m1_subset_1(sK5(k4_tarski(sK1,sK2),sK0),u1_struct_0(sK0))
    | ~ spl11_0
    | ~ spl11_44 ),
    inference(resolution,[],[f339,f217])).

fof(f217,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k8_filter_1(sK0))
      | m1_subset_1(sK5(X1,sK0),u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f94,f95,f93,f214])).

fof(f214,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k8_filter_1(sK0))
      | m1_subset_1(sK5(X1,sK0),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f117,f152])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_1_0_filter_1(X1))
      | m1_subset_1(sK5(X0,X1),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f2518,plain,
    ( spl11_44
    | spl11_4
    | ~ spl11_26 ),
    inference(avatar_split_clause,[],[f2514,f222,f155,f291])).

fof(f222,plain,
    ( spl11_26
  <=> ! [X1,X0] :
        ( k1_domain_1(X0,u1_struct_0(sK0),X1,sK2) = k4_tarski(X1,sK2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f2514,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2) = k4_tarski(sK1,sK2)
    | ~ spl11_26 ),
    inference(resolution,[],[f223,f96])).

fof(f96,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f74])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0)
        | k1_domain_1(X0,u1_struct_0(sK0),X1,sK2) = k4_tarski(X1,sK2) )
    | ~ spl11_26 ),
    inference(avatar_component_clause,[],[f222])).

fof(f2499,plain,
    ( spl11_4
    | spl11_26 ),
    inference(avatar_split_clause,[],[f2496,f222,f155])).

fof(f2496,plain,(
    ! [X0,X1] :
      ( k1_domain_1(X0,u1_struct_0(sK0),X1,sK2) = k4_tarski(X1,sK2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(u1_struct_0(sK0))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f97,f130])).

fof(f97,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f74])).

fof(f233,plain,
    ( spl11_1
    | ~ spl11_20 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f139,f228])).

fof(f228,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0))
    | ~ spl11_20 ),
    inference(forward_demodulation,[],[f187,f152])).

fof(f187,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),a_1_0_filter_1(sK0))
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl11_20
  <=> r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),a_1_0_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f139,plain,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl11_1
  <=> ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f220,plain,(
    spl11_11 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl11_11 ),
    inference(subsumption_resolution,[],[f95,f212])).

fof(f212,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl11_11 ),
    inference(resolution,[],[f205,f103])).

fof(f103,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t32_filter_1.p',dt_l3_lattices)).

fof(f205,plain,
    ( ~ l1_lattices(sK0)
    | ~ spl11_11 ),
    inference(resolution,[],[f169,f101])).

fof(f101,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t32_filter_1.p',dt_l1_lattices)).

fof(f169,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl11_11
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f210,plain,(
    ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f93,f166])).

fof(f166,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f208,plain,(
    spl11_19 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f97,f184])).

fof(f184,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl11_19
  <=> ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f204,plain,(
    spl11_17 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f96,f181])).

fof(f181,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl11_17
  <=> ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f200,plain,(
    spl11_15 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f95,f178])).

fof(f178,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f177])).

fof(f190,plain,(
    spl11_13 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f94,f175])).

fof(f175,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f174])).

fof(f188,plain,
    ( spl11_8
    | ~ spl11_13
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_19
    | spl11_20
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f172,f148,f186,f183,f180,f177,f174,f165])).

fof(f172,plain,
    ( r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),a_1_0_filter_1(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f149,f136])).

fof(f136,plain,(
    ! [X2,X3,X1] :
      ( ~ r3_lattices(X1,X2,X3)
      | r2_hidden(k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3),a_1_0_filter_1(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_1_0_filter_1(X1))
      | ~ r3_lattices(X1,X2,X3)
      | k1_domain_1(u1_struct_0(X1),u1_struct_0(X1),X2,X3) != X0
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f149,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f170,plain,
    ( spl11_8
    | ~ spl11_11
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f161,f155,f168,f165])).

fof(f161,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_4 ),
    inference(resolution,[],[f156,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/filter_1__t32_filter_1.p',fc2_struct_0)).

fof(f156,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f155])).

fof(f150,plain,
    ( spl11_0
    | spl11_2 ),
    inference(avatar_split_clause,[],[f98,f148,f145])).

fof(f98,plain,
    ( r3_lattices(sK0,sK1,sK2)
    | r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

fof(f143,plain,
    ( ~ spl11_1
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f99,f141,f138])).

fof(f141,plain,
    ( spl11_3
  <=> ~ r3_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f99,plain,
    ( ~ r3_lattices(sK0,sK1,sK2)
    | ~ r2_hidden(k1_domain_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1,sK2),k8_filter_1(sK0)) ),
    inference(cnf_transformation,[],[f74])).
%------------------------------------------------------------------------------
