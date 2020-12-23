%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t43_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:55 EDT 2019

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 699 expanded)
%              Number of leaves         :   30 ( 218 expanded)
%              Depth                    :   28
%              Number of atoms          :  888 (4372 expanded)
%              Number of equality atoms :  101 (1169 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5472,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f196,f352,f585,f4991,f4996,f5001,f5006,f5364,f5370,f5377,f5470])).

fof(f5470,plain,
    ( spl12_3
    | spl12_7
    | ~ spl12_320 ),
    inference(avatar_contradiction_clause,[],[f5469])).

fof(f5469,plain,
    ( $false
    | ~ spl12_3
    | ~ spl12_7
    | ~ spl12_320 ),
    inference(subsumption_resolution,[],[f5468,f5408])).

fof(f5408,plain,
    ( k16_lattice3(sK0,k1_tarski(sK1)) != sK1
    | ~ spl12_3
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f5407,f215])).

fof(f215,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl12_7
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f5407,plain,
    ( k16_lattice3(sK0,k1_tarski(sK1)) != sK1
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f5406,f122])).

fof(f122,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,
    ( ( k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1
      | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1 )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f43,f85,f84])).

fof(f84,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
              | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != X1
            | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),sK1)) != sK1
          | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),sK1)) != sK1 )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
              & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',t43_lattice3)).

fof(f5406,plain,
    ( k16_lattice3(sK0,k1_tarski(sK1)) != sK1
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_3 ),
    inference(superposition,[],[f195,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',redefinition_k6_domain_1)).

fof(f195,plain,
    ( k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl12_3
  <=> k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f5468,plain,
    ( k16_lattice3(sK0,k1_tarski(sK1)) = sK1
    | ~ spl12_3
    | ~ spl12_7
    | ~ spl12_320 ),
    inference(subsumption_resolution,[],[f5467,f122])).

fof(f5467,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k16_lattice3(sK0,k1_tarski(sK1)) = sK1
    | ~ spl12_3
    | ~ spl12_7
    | ~ spl12_320 ),
    inference(subsumption_resolution,[],[f5465,f180])).

fof(f180,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f179])).

fof(f179,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f159])).

fof(f159,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK6(X0,X1) != X0
            | ~ r2_hidden(sK6(X0,X1),X1) )
          & ( sK6(X0,X1) = X0
            | r2_hidden(sK6(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f101,f102])).

fof(f102,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK6(X0,X1) != X0
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( sK6(X0,X1) = X0
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',d1_tarski)).

fof(f5465,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k16_lattice3(sK0,k1_tarski(sK1)) = sK1
    | ~ spl12_3
    | ~ spl12_7
    | ~ spl12_320 ),
    inference(resolution,[],[f5464,f2639])).

fof(f2639,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k16_lattice3(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f2638,f118])).

fof(f118,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f2638,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k16_lattice3(sK0,X1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2637,f119])).

fof(f119,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f2637,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k16_lattice3(sK0,X1) = X0
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2636,f121])).

fof(f121,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f2636,plain,(
    ! [X0,X1] :
      ( ~ r3_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k16_lattice3(sK0,X1) = X0
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f138,f120])).

fof(f120,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f86])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k16_lattice3(X0,X2) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
              | ~ r3_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
              | ~ r3_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',t42_lattice3)).

fof(f5464,plain,
    ( r3_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ spl12_3
    | ~ spl12_7
    | ~ spl12_320 ),
    inference(subsumption_resolution,[],[f5463,f118])).

fof(f5463,plain,
    ( r3_lattice3(sK0,sK1,k1_tarski(sK1))
    | v2_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_7
    | ~ spl12_320 ),
    inference(subsumption_resolution,[],[f5462,f121])).

fof(f5462,plain,
    ( r3_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_7
    | ~ spl12_320 ),
    inference(subsumption_resolution,[],[f5461,f122])).

fof(f5461,plain,
    ( r3_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_7
    | ~ spl12_320 ),
    inference(subsumption_resolution,[],[f5460,f5360])).

fof(f5360,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | ~ spl12_320 ),
    inference(avatar_component_clause,[],[f5359])).

fof(f5359,plain,
    ( spl12_320
  <=> r1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_320])])).

fof(f5460,plain,
    ( ~ r1_lattices(sK0,sK1,sK1)
    | r3_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_3
    | ~ spl12_7 ),
    inference(superposition,[],[f146,f5455])).

fof(f5455,plain,
    ( sK1 = sK3(sK0,sK1,k1_tarski(sK1))
    | ~ spl12_3
    | ~ spl12_7 ),
    inference(resolution,[],[f5447,f181])).

fof(f181,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f158])).

fof(f158,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f103])).

fof(f5447,plain,
    ( r2_hidden(sK3(sK0,sK1,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl12_3
    | ~ spl12_7 ),
    inference(subsumption_resolution,[],[f5432,f5408])).

fof(f5432,plain,
    ( k16_lattice3(sK0,k1_tarski(sK1)) = sK1
    | r2_hidden(sK3(sK0,sK1,k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(resolution,[],[f5417,f180])).

fof(f5417,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK1,X9)
      | k16_lattice3(sK0,X9) = sK1
      | r2_hidden(sK3(sK0,sK1,X9),X9) ) ),
    inference(resolution,[],[f2976,f122])).

fof(f2976,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ r2_hidden(X6,X7)
      | k16_lattice3(sK0,X7) = X6
      | r2_hidden(sK3(sK0,X6,X7),X7) ) ),
    inference(subsumption_resolution,[],[f2975,f118])).

fof(f2975,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k16_lattice3(sK0,X7) = X6
      | r2_hidden(sK3(sK0,X6,X7),X7)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2970,f121])).

fof(f2970,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k16_lattice3(sK0,X7) = X6
      | r2_hidden(sK3(sK0,X6,X7),X7)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2969])).

fof(f2969,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | k16_lattice3(sK0,X7) = X6
      | r2_hidden(sK3(sK0,X6,X7),X7)
      | ~ m1_subset_1(X6,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2639,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,X2)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
                  & r2_hidden(sK3(X0,X1,X2),X2)
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f92,f93])).

fof(f93,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
        & r2_hidden(sK3(X0,X1,X2),X2)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',d16_lattice3)).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,sK3(X0,X1,X2))
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f5377,plain,
    ( spl12_13
    | ~ spl12_318 ),
    inference(avatar_contradiction_clause,[],[f5376])).

fof(f5376,plain,
    ( $false
    | ~ spl12_13
    | ~ spl12_318 ),
    inference(subsumption_resolution,[],[f5375,f351])).

fof(f351,plain,
    ( k15_lattice3(sK0,k1_tarski(sK1)) != sK1
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl12_13
  <=> k15_lattice3(sK0,k1_tarski(sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f5375,plain,
    ( k15_lattice3(sK0,k1_tarski(sK1)) = sK1
    | ~ spl12_318 ),
    inference(subsumption_resolution,[],[f5374,f122])).

fof(f5374,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_tarski(sK1)) = sK1
    | ~ spl12_318 ),
    inference(subsumption_resolution,[],[f5372,f180])).

fof(f5372,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_tarski(sK1)) = sK1
    | ~ spl12_318 ),
    inference(resolution,[],[f5357,f2534])).

fof(f2534,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f2533,f118])).

fof(f2533,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2532,f119])).

fof(f2532,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k15_lattice3(sK0,X1) = X0
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2531,f121])).

fof(f2531,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK0,X0,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | k15_lattice3(sK0,X1) = X0
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f137,f120])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X2) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',t41_lattice3)).

fof(f5357,plain,
    ( r4_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ spl12_318 ),
    inference(avatar_component_clause,[],[f5356])).

fof(f5356,plain,
    ( spl12_318
  <=> r4_lattice3(sK0,sK1,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_318])])).

fof(f5370,plain,
    ( ~ spl12_296
    | spl12_321 ),
    inference(avatar_contradiction_clause,[],[f5369])).

fof(f5369,plain,
    ( $false
    | ~ spl12_296
    | ~ spl12_321 ),
    inference(subsumption_resolution,[],[f5366,f122])).

fof(f5366,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl12_296
    | ~ spl12_321 ),
    inference(resolution,[],[f5363,f4990])).

fof(f4990,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl12_296 ),
    inference(avatar_component_clause,[],[f4989])).

fof(f4989,plain,
    ( spl12_296
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_296])])).

fof(f5363,plain,
    ( ~ r1_lattices(sK0,sK1,sK1)
    | ~ spl12_321 ),
    inference(avatar_component_clause,[],[f5362])).

fof(f5362,plain,
    ( spl12_321
  <=> ~ r1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_321])])).

fof(f5364,plain,
    ( spl12_318
    | ~ spl12_321
    | spl12_13 ),
    inference(avatar_split_clause,[],[f5351,f350,f5362,f5356])).

fof(f5351,plain,
    ( ~ r1_lattices(sK0,sK1,sK1)
    | r4_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f5350,f118])).

fof(f5350,plain,
    ( ~ r1_lattices(sK0,sK1,sK1)
    | r4_lattice3(sK0,sK1,k1_tarski(sK1))
    | v2_struct_0(sK0)
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f5349,f121])).

fof(f5349,plain,
    ( ~ r1_lattices(sK0,sK1,sK1)
    | r4_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f5348,f122])).

fof(f5348,plain,
    ( ~ r1_lattices(sK0,sK1,sK1)
    | r4_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_13 ),
    inference(superposition,[],[f142,f5344])).

fof(f5344,plain,
    ( sK1 = sK2(sK0,sK1,k1_tarski(sK1))
    | ~ spl12_13 ),
    inference(resolution,[],[f5336,f181])).

fof(f5336,plain,
    ( r2_hidden(sK2(sK0,sK1,k1_tarski(sK1)),k1_tarski(sK1))
    | ~ spl12_13 ),
    inference(subsumption_resolution,[],[f5321,f351])).

fof(f5321,plain,
    ( k15_lattice3(sK0,k1_tarski(sK1)) = sK1
    | r2_hidden(sK2(sK0,sK1,k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(resolution,[],[f5299,f180])).

fof(f5299,plain,(
    ! [X9] :
      ( ~ r2_hidden(sK1,X9)
      | k15_lattice3(sK0,X9) = sK1
      | r2_hidden(sK2(sK0,sK1,X9),X9) ) ),
    inference(resolution,[],[f2908,f122])).

fof(f2908,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X3)
      | k15_lattice3(sK0,X3) = X2
      | r2_hidden(sK2(sK0,X2,X3),X3) ) ),
    inference(subsumption_resolution,[],[f2907,f118])).

fof(f2907,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | r2_hidden(sK2(sK0,X2,X3),X3)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2903,f121])).

fof(f2903,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | r2_hidden(sK2(sK0,X2,X3),X3)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2902])).

fof(f2902,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | k15_lattice3(sK0,X3) = X2
      | r2_hidden(sK2(sK0,X2,X3),X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2534,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK2(X0,X1,X2),X1)
                  & r2_hidden(sK2(X0,X1,X2),X2)
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f88,f89])).

fof(f89,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),X2)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',d17_lattice3)).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK2(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f5006,plain,(
    spl12_295 ),
    inference(avatar_contradiction_clause,[],[f5005])).

fof(f5005,plain,
    ( $false
    | ~ spl12_295 ),
    inference(subsumption_resolution,[],[f5004,f121])).

fof(f5004,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl12_295 ),
    inference(subsumption_resolution,[],[f5003,f118])).

fof(f5003,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl12_295 ),
    inference(subsumption_resolution,[],[f5002,f119])).

fof(f5002,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl12_295 ),
    inference(resolution,[],[f4987,f135])).

fof(f135,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',cc1_lattices)).

fof(f4987,plain,
    ( ~ v9_lattices(sK0)
    | ~ spl12_295 ),
    inference(avatar_component_clause,[],[f4986])).

fof(f4986,plain,
    ( spl12_295
  <=> ~ v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_295])])).

fof(f5001,plain,(
    spl12_293 ),
    inference(avatar_contradiction_clause,[],[f5000])).

fof(f5000,plain,
    ( $false
    | ~ spl12_293 ),
    inference(subsumption_resolution,[],[f4999,f121])).

fof(f4999,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl12_293 ),
    inference(subsumption_resolution,[],[f4998,f118])).

fof(f4998,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl12_293 ),
    inference(subsumption_resolution,[],[f4997,f119])).

fof(f4997,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl12_293 ),
    inference(resolution,[],[f4981,f134])).

fof(f134,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4981,plain,
    ( ~ v8_lattices(sK0)
    | ~ spl12_293 ),
    inference(avatar_component_clause,[],[f4980])).

fof(f4980,plain,
    ( spl12_293
  <=> ~ v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_293])])).

fof(f4996,plain,(
    spl12_291 ),
    inference(avatar_contradiction_clause,[],[f4995])).

fof(f4995,plain,
    ( $false
    | ~ spl12_291 ),
    inference(subsumption_resolution,[],[f4994,f121])).

fof(f4994,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl12_291 ),
    inference(subsumption_resolution,[],[f4993,f118])).

fof(f4993,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl12_291 ),
    inference(subsumption_resolution,[],[f4992,f119])).

fof(f4992,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl12_291 ),
    inference(resolution,[],[f4975,f132])).

fof(f132,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4975,plain,
    ( ~ v6_lattices(sK0)
    | ~ spl12_291 ),
    inference(avatar_component_clause,[],[f4974])).

fof(f4974,plain,
    ( spl12_291
  <=> ~ v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_291])])).

fof(f4991,plain,
    ( ~ spl12_291
    | ~ spl12_293
    | ~ spl12_295
    | spl12_296 ),
    inference(avatar_split_clause,[],[f4969,f4989,f4986,f4980,f4974])).

fof(f4969,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f4968,f118])).

fof(f4968,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f4967,f121])).

fof(f4967,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X0)
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f4966])).

fof(f4966,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | ~ v6_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f4700,f183])).

fof(f183,plain,(
    ! [X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(condensation,[],[f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',reflexivity_r3_lattices)).

fof(f4700,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f4699,f118])).

fof(f4699,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f4698,f121])).

fof(f4698,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f2754,f119])).

fof(f2754,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f2753,f134])).

fof(f2753,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f2752,f132])).

fof(f2752,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f2751])).

fof(f2751,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f167,f135])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',redefinition_r3_lattices)).

fof(f585,plain,(
    ~ spl12_6 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f583,f121])).

fof(f583,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl12_6 ),
    inference(resolution,[],[f581,f128])).

fof(f128,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',dt_l3_lattices)).

fof(f581,plain,
    ( ~ l2_lattices(sK0)
    | ~ spl12_6 ),
    inference(resolution,[],[f580,f126])).

fof(f126,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',dt_l2_lattices)).

fof(f580,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f575,f118])).

fof(f575,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_6 ),
    inference(resolution,[],[f218,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t43_lattice3.p',fc2_struct_0)).

fof(f218,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl12_6
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f352,plain,
    ( spl12_6
    | ~ spl12_13
    | spl12_1 ),
    inference(avatar_split_clause,[],[f345,f188,f350,f217])).

fof(f188,plain,
    ( spl12_1
  <=> k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f345,plain,
    ( k15_lattice3(sK0,k1_tarski(sK1)) != sK1
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f344,f122])).

fof(f344,plain,
    ( k15_lattice3(sK0,k1_tarski(sK1)) != sK1
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl12_1 ),
    inference(superposition,[],[f189,f152])).

fof(f189,plain,
    ( k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f188])).

fof(f196,plain,
    ( ~ spl12_1
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f123,f194,f188])).

fof(f123,plain,
    ( k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1
    | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != sK1 ),
    inference(cnf_transformation,[],[f86])).
%------------------------------------------------------------------------------
