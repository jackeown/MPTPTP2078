%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t53_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:03 EDT 2019

% Result     : Theorem 2.78s
% Output     : Refutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  266 ( 936 expanded)
%              Number of leaves         :   45 ( 357 expanded)
%              Depth                    :   20
%              Number of atoms          : 1278 (6215 expanded)
%              Number of equality atoms :   55 (  76 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26731,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f407,f410,f922,f1118,f1733,f1738,f1837,f1859,f1873,f1934,f1951,f1956,f1959,f1964,f2000,f2010,f26589,f26634,f26686,f26730])).

fof(f26730,plain,
    ( ~ spl8_10
    | ~ spl8_70
    | ~ spl8_146
    | spl8_167
    | ~ spl8_2146 ),
    inference(avatar_contradiction_clause,[],[f26729])).

fof(f26729,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_146
    | ~ spl8_167
    | ~ spl8_2146 ),
    inference(subsumption_resolution,[],[f26728,f118])).

fof(f118,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,
    ( ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    & r3_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v17_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f103,f102,f101])).

fof(f101,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
                & r3_lattices(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(sK0,k7_lattices(sK0,X2),k7_lattices(sK0,X1))
              & r3_lattices(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v17_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,sK1))
            & r3_lattices(X0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
          & r3_lattices(X0,X1,X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ~ r3_lattices(X0,k7_lattices(X0,sK2),k7_lattices(X0,X1))
        & r3_lattices(X0,X1,sK2)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1))
              & r3_lattices(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                 => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
               => r3_lattices(X0,k7_lattices(X0,X2),k7_lattices(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t53_lattices)).

fof(f26728,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_146
    | ~ spl8_167
    | ~ spl8_2146 ),
    inference(subsumption_resolution,[],[f26727,f910])).

fof(f910,plain,
    ( v6_lattices(sK0)
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f909])).

fof(f909,plain,
    ( spl8_70
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f26727,plain,
    ( ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_10
    | ~ spl8_146
    | ~ spl8_167
    | ~ spl8_2146 ),
    inference(subsumption_resolution,[],[f26726,f400])).

fof(f400,plain,
    ( l1_lattices(sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl8_10
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f26726,plain,
    ( ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_146
    | ~ spl8_167
    | ~ spl8_2146 ),
    inference(subsumption_resolution,[],[f26725,f122])).

fof(f122,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f104])).

fof(f26725,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_146
    | ~ spl8_167
    | ~ spl8_2146 ),
    inference(subsumption_resolution,[],[f26724,f1833])).

fof(f1833,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_146 ),
    inference(avatar_component_clause,[],[f1832])).

fof(f1832,plain,
    ( spl8_146
  <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).

fof(f26724,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_167
    | ~ spl8_2146 ),
    inference(subsumption_resolution,[],[f26707,f1993])).

fof(f1993,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k5_lattices(sK0)
    | ~ spl8_167 ),
    inference(avatar_component_clause,[],[f1992])).

fof(f1992,plain,
    ( spl8_167
  <=> k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_167])])).

fof(f26707,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2146 ),
    inference(superposition,[],[f169,f26582])).

fof(f26582,plain,
    ( k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
    | ~ spl8_2146 ),
    inference(avatar_component_clause,[],[f26581])).

fof(f26581,plain,
    ( spl8_2146
  <=> k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2146])])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',redefinition_k4_lattices)).

fof(f26686,plain,
    ( ~ spl8_92
    | spl8_2145
    | ~ spl8_2148 ),
    inference(avatar_contradiction_clause,[],[f26685])).

fof(f26685,plain,
    ( $false
    | ~ spl8_92
    | ~ spl8_2145
    | ~ spl8_2148 ),
    inference(subsumption_resolution,[],[f26684,f118])).

fof(f26684,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_92
    | ~ spl8_2145
    | ~ spl8_2148 ),
    inference(subsumption_resolution,[],[f26683,f119])).

fof(f119,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f26683,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_92
    | ~ spl8_2145
    | ~ spl8_2148 ),
    inference(subsumption_resolution,[],[f26682,f1103])).

fof(f1103,plain,
    ( v13_lattices(sK0)
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f1102])).

fof(f1102,plain,
    ( spl8_92
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f26682,plain,
    ( ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2145
    | ~ spl8_2148 ),
    inference(subsumption_resolution,[],[f26681,f121])).

fof(f121,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f26681,plain,
    ( ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2145
    | ~ spl8_2148 ),
    inference(subsumption_resolution,[],[f26679,f26585])).

fof(f26585,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl8_2148 ),
    inference(avatar_component_clause,[],[f26584])).

fof(f26584,plain,
    ( spl8_2148
  <=> m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2148])])).

fof(f26679,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2145 ),
    inference(resolution,[],[f26576,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( r3_lattices(X0,k5_lattices(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_lattices(X0,k5_lattices(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t41_lattices)).

fof(f26576,plain,
    ( ~ r3_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | ~ spl8_2145 ),
    inference(avatar_component_clause,[],[f26575])).

fof(f26575,plain,
    ( spl8_2145
  <=> ~ r3_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2145])])).

fof(f26634,plain,
    ( ~ spl8_12
    | ~ spl8_146
    | spl8_2149 ),
    inference(avatar_contradiction_clause,[],[f26633])).

fof(f26633,plain,
    ( $false
    | ~ spl8_12
    | ~ spl8_146
    | ~ spl8_2149 ),
    inference(subsumption_resolution,[],[f26632,f1833])).

fof(f26632,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_12
    | ~ spl8_2149 ),
    inference(subsumption_resolution,[],[f26629,f122])).

fof(f26629,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_12
    | ~ spl8_2149 ),
    inference(resolution,[],[f26588,f406])).

fof(f406,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_lattices(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl8_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_subset_1(k2_lattices(sK0,X1,X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f26588,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | ~ spl8_2149 ),
    inference(avatar_component_clause,[],[f26587])).

fof(f26587,plain,
    ( spl8_2149
  <=> ~ m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2149])])).

fof(f26589,plain,
    ( ~ spl8_2145
    | spl8_2146
    | ~ spl8_2149
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_146
    | ~ spl8_150
    | ~ spl8_158
    | ~ spl8_164 ),
    inference(avatar_split_clause,[],[f26570,f1949,f1932,f1857,f1832,f909,f399,f26587,f26581,f26575])).

fof(f1857,plain,
    ( spl8_150
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).

fof(f1932,plain,
    ( spl8_158
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,X1,X2),k2_lattices(sK0,X0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_158])])).

fof(f1949,plain,
    ( spl8_164
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X5,X6)
        | X5 = X6
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X6,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_164])])).

fof(f26570,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
    | ~ r3_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_146
    | ~ spl8_150
    | ~ spl8_158
    | ~ spl8_164 ),
    inference(subsumption_resolution,[],[f26565,f1858])).

fof(f1858,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl8_150 ),
    inference(avatar_component_clause,[],[f1857])).

fof(f26565,plain,
    ( ~ m1_subset_1(k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),u1_struct_0(sK0))
    | k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k5_lattices(sK0),k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_146
    | ~ spl8_158
    | ~ spl8_164 ),
    inference(resolution,[],[f26312,f1950])).

fof(f1950,plain,
    ( ! [X6,X5] :
        ( ~ r1_lattices(sK0,X5,X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | X5 = X6
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X6,X5) )
    | ~ spl8_164 ),
    inference(avatar_component_clause,[],[f1949])).

fof(f26312,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0))
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_146
    | ~ spl8_158 ),
    inference(subsumption_resolution,[],[f26287,f1833])).

fof(f26287,plain,
    ( r1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_146
    | ~ spl8_158 ),
    inference(superposition,[],[f24807,f2180])).

fof(f2180,plain,
    ( k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_146 ),
    inference(subsumption_resolution,[],[f2176,f123])).

fof(f123,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f104])).

fof(f2176,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k4_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k5_lattices(sK0)
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_146 ),
    inference(resolution,[],[f1982,f1833])).

fof(f1982,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(k7_lattices(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k4_lattices(sK0,X4,k7_lattices(sK0,X4)) = k5_lattices(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f1981,f118])).

fof(f1981,plain,
    ( ! [X4] :
        ( k4_lattices(sK0,X4,k7_lattices(sK0,X4)) = k5_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X4),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f1980,f119])).

fof(f1980,plain,
    ( ! [X4] :
        ( k4_lattices(sK0,X4,k7_lattices(sK0,X4)) = k5_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X4),u1_struct_0(sK0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f1979,f120])).

fof(f120,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f104])).

fof(f1979,plain,
    ( ! [X4] :
        ( k4_lattices(sK0,X4,k7_lattices(sK0,X4)) = k5_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X4),u1_struct_0(sK0))
        | ~ v17_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f1978,f121])).

fof(f1978,plain,
    ( ! [X4] :
        ( k4_lattices(sK0,X4,k7_lattices(sK0,X4)) = k5_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X4),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v17_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(duplicate_literal_removal,[],[f1965])).

fof(f1965,plain,
    ( ! [X4] :
        ( k4_lattices(sK0,X4,k7_lattices(sK0,X4)) = k5_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v17_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(superposition,[],[f928,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k7_lattices(X0,X1),X1) = k5_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t47_lattices)).

fof(f928,plain,
    ( ! [X0,X1] :
        ( k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f927,f118])).

fof(f927,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f925,f400])).

fof(f925,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
        | v2_struct_0(sK0) )
    | ~ spl8_70 ),
    inference(resolution,[],[f910,f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',commutativity_k4_lattices)).

fof(f24807,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_158 ),
    inference(subsumption_resolution,[],[f24806,f118])).

fof(f24806,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_158 ),
    inference(subsumption_resolution,[],[f24805,f910])).

fof(f24805,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_158 ),
    inference(subsumption_resolution,[],[f24804,f400])).

fof(f24804,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_158 ),
    inference(subsumption_resolution,[],[f24784,f123])).

fof(f24784,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_158 ),
    inference(duplicate_literal_removal,[],[f24783])).

fof(f24783,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k4_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_158 ),
    inference(superposition,[],[f23731,f169])).

fof(f23731,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_158 ),
    inference(subsumption_resolution,[],[f23730,f123])).

fof(f23730,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl8_158 ),
    inference(subsumption_resolution,[],[f23729,f122])).

fof(f23729,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,sK1,X0),k2_lattices(sK0,sK2,X0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl8_158 ),
    inference(resolution,[],[f124,f1933])).

fof(f1933,plain,
    ( ! [X2,X0,X1] :
        ( ~ r3_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,X1,X2),k2_lattices(sK0,X0,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_158 ),
    inference(avatar_component_clause,[],[f1932])).

fof(f124,plain,(
    r3_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f104])).

fof(f2010,plain,(
    spl8_147 ),
    inference(avatar_contradiction_clause,[],[f2009])).

fof(f2009,plain,
    ( $false
    | ~ spl8_147 ),
    inference(subsumption_resolution,[],[f2008,f118])).

fof(f2008,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_147 ),
    inference(subsumption_resolution,[],[f2007,f121])).

fof(f2007,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_147 ),
    inference(subsumption_resolution,[],[f2005,f123])).

fof(f2005,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_147 ),
    inference(resolution,[],[f1836,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',dt_k7_lattices)).

fof(f1836,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_147 ),
    inference(avatar_component_clause,[],[f1835])).

fof(f1835,plain,
    ( spl8_147
  <=> ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).

fof(f2000,plain,
    ( ~ spl8_147
    | ~ spl8_167
    | ~ spl8_10
    | ~ spl8_70
    | spl8_139 ),
    inference(avatar_split_clause,[],[f1999,f1693,f909,f399,f1992,f1835])).

fof(f1693,plain,
    ( spl8_139
  <=> k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_139])])).

fof(f1999,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k5_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_139 ),
    inference(subsumption_resolution,[],[f1970,f122])).

fof(f1970,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) != k5_lattices(sK0)
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_10
    | ~ spl8_70
    | ~ spl8_139 ),
    inference(superposition,[],[f1694,f928])).

fof(f1694,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k5_lattices(sK0)
    | ~ spl8_139 ),
    inference(avatar_component_clause,[],[f1693])).

fof(f1964,plain,(
    spl8_161 ),
    inference(avatar_contradiction_clause,[],[f1963])).

fof(f1963,plain,
    ( $false
    | ~ spl8_161 ),
    inference(subsumption_resolution,[],[f1962,f121])).

fof(f1962,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl8_161 ),
    inference(subsumption_resolution,[],[f1961,f118])).

fof(f1961,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl8_161 ),
    inference(subsumption_resolution,[],[f1960,f119])).

fof(f1960,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl8_161 ),
    inference(resolution,[],[f1941,f142])).

fof(f142,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',cc1_lattices)).

fof(f1941,plain,
    ( ~ v4_lattices(sK0)
    | ~ spl8_161 ),
    inference(avatar_component_clause,[],[f1940])).

fof(f1940,plain,
    ( spl8_161
  <=> ~ v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_161])])).

fof(f1959,plain,(
    spl8_163 ),
    inference(avatar_contradiction_clause,[],[f1958])).

fof(f1958,plain,
    ( $false
    | ~ spl8_163 ),
    inference(subsumption_resolution,[],[f1957,f121])).

fof(f1957,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl8_163 ),
    inference(resolution,[],[f1947,f133])).

fof(f133,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',dt_l3_lattices)).

fof(f1947,plain,
    ( ~ l2_lattices(sK0)
    | ~ spl8_163 ),
    inference(avatar_component_clause,[],[f1946])).

fof(f1946,plain,
    ( spl8_163
  <=> ~ l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_163])])).

fof(f1956,plain,(
    spl8_157 ),
    inference(avatar_contradiction_clause,[],[f1955])).

fof(f1955,plain,
    ( $false
    | ~ spl8_157 ),
    inference(subsumption_resolution,[],[f1954,f121])).

fof(f1954,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl8_157 ),
    inference(subsumption_resolution,[],[f1953,f118])).

fof(f1953,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl8_157 ),
    inference(subsumption_resolution,[],[f1952,f119])).

fof(f1952,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl8_157 ),
    inference(resolution,[],[f1930,f145])).

fof(f145,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1930,plain,
    ( ~ v7_lattices(sK0)
    | ~ spl8_157 ),
    inference(avatar_component_clause,[],[f1929])).

fof(f1929,plain,
    ( spl8_157
  <=> ~ v7_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_157])])).

fof(f1951,plain,
    ( ~ spl8_161
    | ~ spl8_163
    | spl8_164
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(avatar_split_clause,[],[f1935,f1720,f1714,f909,f1949,f1946,f1940])).

fof(f1714,plain,
    ( spl8_140
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_140])])).

fof(f1720,plain,
    ( spl8_142
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).

fof(f1935,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X6,X5)
        | X5 = X6
        | ~ r1_lattices(sK0,X5,X6)
        | ~ l2_lattices(sK0)
        | ~ v4_lattices(sK0) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f1918,f118])).

fof(f1918,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X6,X5)
        | X5 = X6
        | ~ r1_lattices(sK0,X5,X6)
        | ~ l2_lattices(sK0)
        | ~ v4_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(duplicate_literal_removal,[],[f1917])).

fof(f1917,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X6,X5)
        | X5 = X6
        | ~ r1_lattices(sK0,X5,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | ~ v4_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(resolution,[],[f1748,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t26_lattices)).

fof(f1748,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f1747,f118])).

fof(f1747,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f1746,f910])).

fof(f1746,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,X1)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f1745,f1715])).

fof(f1715,plain,
    ( v8_lattices(sK0)
    | ~ spl8_140 ),
    inference(avatar_component_clause,[],[f1714])).

fof(f1745,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,X0,X1)
        | ~ v8_lattices(sK0)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f1744,f121])).

fof(f1744,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,X0,X1)
        | ~ v8_lattices(sK0)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_142 ),
    inference(resolution,[],[f1721,f166])).

fof(f166,plain,(
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
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
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
    inference(nnf_transformation,[],[f85])).

fof(f85,plain,(
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
    inference(flattening,[],[f84])).

fof(f84,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',redefinition_r3_lattices)).

fof(f1721,plain,
    ( v9_lattices(sK0)
    | ~ spl8_142 ),
    inference(avatar_component_clause,[],[f1720])).

fof(f1934,plain,
    ( ~ spl8_157
    | spl8_158
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(avatar_split_clause,[],[f1924,f1720,f1714,f909,f1932,f1929])).

fof(f1924,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X0)
        | r1_lattices(sK0,k2_lattices(sK0,X1,X2),k2_lattices(sK0,X0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v7_lattices(sK0) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f1923,f118])).

fof(f1923,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X0)
        | r1_lattices(sK0,k2_lattices(sK0,X1,X2),k2_lattices(sK0,X0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v7_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f1922,f1715])).

fof(f1922,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X0)
        | r1_lattices(sK0,k2_lattices(sK0,X1,X2),k2_lattices(sK0,X0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v8_lattices(sK0)
        | ~ v7_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f1921,f1721])).

fof(f1921,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X0)
        | r1_lattices(sK0,k2_lattices(sK0,X1,X2),k2_lattices(sK0,X0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v9_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v7_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f1920,f121])).

fof(f1920,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X0)
        | r1_lattices(sK0,k2_lattices(sK0,X1,X2),k2_lattices(sK0,X0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v7_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(duplicate_literal_removal,[],[f1915])).

fof(f1915,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X1,X0)
        | r1_lattices(sK0,k2_lattices(sK0,X1,X2),k2_lattices(sK0,X0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v7_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_70
    | ~ spl8_140
    | ~ spl8_142 ),
    inference(resolution,[],[f1748,f148])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t27_lattices)).

fof(f1873,plain,(
    ~ spl8_148 ),
    inference(avatar_contradiction_clause,[],[f1865])).

fof(f1865,plain,
    ( $false
    | ~ spl8_148 ),
    inference(resolution,[],[f1864,f122])).

fof(f1864,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ spl8_148 ),
    inference(subsumption_resolution,[],[f1863,f118])).

fof(f1863,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_148 ),
    inference(subsumption_resolution,[],[f1862,f121])).

fof(f1862,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_148 ),
    inference(duplicate_literal_removal,[],[f1860])).

fof(f1860,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_148 ),
    inference(resolution,[],[f1852,f160])).

fof(f1852,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_148 ),
    inference(avatar_component_clause,[],[f1851])).

fof(f1851,plain,
    ( spl8_148
  <=> ! [X0] :
        ( ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_148])])).

fof(f1859,plain,
    ( spl8_148
    | spl8_150
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(avatar_split_clause,[],[f1849,f909,f399,f1857,f1851])).

fof(f1849,plain,
    ( ! [X0] :
        ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f1848,f118])).

fof(f1848,plain,
    ( ! [X0] :
        ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f1847,f119])).

fof(f1847,plain,
    ( ! [X0] :
        ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f1846,f120])).

fof(f1846,plain,
    ( ! [X0] :
        ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v17_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f1843,f121])).

fof(f1843,plain,
    ( ! [X0] :
        ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v17_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(duplicate_literal_removal,[],[f1842])).

fof(f1842,plain,
    ( ! [X0] :
        ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(k7_lattices(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v17_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(superposition,[],[f930,f151])).

fof(f930,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_lattices(sK0,X3,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f929,f118])).

fof(f929,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | m1_subset_1(k4_lattices(sK0,X3,X2),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_10
    | ~ spl8_70 ),
    inference(subsumption_resolution,[],[f926,f400])).

fof(f926,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | m1_subset_1(k4_lattices(sK0,X3,X2),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl8_70 ),
    inference(resolution,[],[f910,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',dt_k4_lattices)).

fof(f1837,plain,
    ( ~ spl8_139
    | ~ spl8_147 ),
    inference(avatar_split_clause,[],[f1830,f1835,f1693])).

fof(f1830,plain,
    ( ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k5_lattices(sK0) ),
    inference(subsumption_resolution,[],[f1829,f122])).

fof(f1829,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) != k5_lattices(sK0) ),
    inference(resolution,[],[f1312,f125])).

fof(f125,plain,(
    ~ r3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) ),
    inference(cnf_transformation,[],[f104])).

fof(f1312,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k4_lattices(sK0,X0,X1) != k5_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f1311,f118])).

fof(f1311,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) != k5_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1310,f119])).

fof(f1310,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) != k5_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1309,f121])).

fof(f1309,plain,(
    ! [X0,X1] :
      ( k4_lattices(sK0,X0,X1) != k5_lattices(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r3_lattices(sK0,X0,k7_lattices(sK0,X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f152,f120])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | k4_lattices(X0,X1,X2) != k5_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,k7_lattices(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                  | ~ r3_lattices(X0,X1,k7_lattices(X0,X2)) )
                & ( r3_lattices(X0,X1,k7_lattices(X0,X2))
                  | k4_lattices(X0,X1,X2) != k5_lattices(X0) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',t52_lattices)).

fof(f1738,plain,(
    spl8_143 ),
    inference(avatar_contradiction_clause,[],[f1737])).

fof(f1737,plain,
    ( $false
    | ~ spl8_143 ),
    inference(subsumption_resolution,[],[f1736,f121])).

fof(f1736,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl8_143 ),
    inference(subsumption_resolution,[],[f1735,f118])).

fof(f1735,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl8_143 ),
    inference(subsumption_resolution,[],[f1734,f119])).

fof(f1734,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl8_143 ),
    inference(resolution,[],[f1724,f147])).

fof(f147,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1724,plain,
    ( ~ v9_lattices(sK0)
    | ~ spl8_143 ),
    inference(avatar_component_clause,[],[f1723])).

fof(f1723,plain,
    ( spl8_143
  <=> ~ v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_143])])).

fof(f1733,plain,(
    spl8_141 ),
    inference(avatar_contradiction_clause,[],[f1732])).

fof(f1732,plain,
    ( $false
    | ~ spl8_141 ),
    inference(subsumption_resolution,[],[f1731,f121])).

fof(f1731,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl8_141 ),
    inference(subsumption_resolution,[],[f1730,f118])).

fof(f1730,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl8_141 ),
    inference(subsumption_resolution,[],[f1729,f119])).

fof(f1729,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl8_141 ),
    inference(resolution,[],[f1718,f146])).

fof(f146,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1718,plain,
    ( ~ v8_lattices(sK0)
    | ~ spl8_141 ),
    inference(avatar_component_clause,[],[f1717])).

fof(f1717,plain,
    ( spl8_141
  <=> ~ v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).

fof(f1118,plain,(
    spl8_93 ),
    inference(avatar_contradiction_clause,[],[f1117])).

fof(f1117,plain,
    ( $false
    | ~ spl8_93 ),
    inference(subsumption_resolution,[],[f1116,f120])).

fof(f1116,plain,
    ( ~ v17_lattices(sK0)
    | ~ spl8_93 ),
    inference(subsumption_resolution,[],[f1115,f121])).

fof(f1115,plain,
    ( ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ spl8_93 ),
    inference(subsumption_resolution,[],[f1114,f118])).

fof(f1114,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ v17_lattices(sK0)
    | ~ spl8_93 ),
    inference(resolution,[],[f1106,f182])).

fof(f182,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X0] :
      ( ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v13_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f139,f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v15_lattices(X0)
      | v13_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',cc4_lattices)).

fof(f139,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',cc5_lattices)).

fof(f1106,plain,
    ( ~ v13_lattices(sK0)
    | ~ spl8_93 ),
    inference(avatar_component_clause,[],[f1105])).

fof(f1105,plain,
    ( spl8_93
  <=> ~ v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).

fof(f922,plain,(
    spl8_71 ),
    inference(avatar_contradiction_clause,[],[f921])).

fof(f921,plain,
    ( $false
    | ~ spl8_71 ),
    inference(subsumption_resolution,[],[f920,f121])).

fof(f920,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl8_71 ),
    inference(subsumption_resolution,[],[f919,f118])).

fof(f919,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl8_71 ),
    inference(subsumption_resolution,[],[f918,f119])).

fof(f918,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl8_71 ),
    inference(resolution,[],[f913,f144])).

fof(f144,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f913,plain,
    ( ~ v6_lattices(sK0)
    | ~ spl8_71 ),
    inference(avatar_component_clause,[],[f912])).

fof(f912,plain,
    ( spl8_71
  <=> ~ v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f410,plain,(
    spl8_11 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f408,f121])).

fof(f408,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl8_11 ),
    inference(resolution,[],[f403,f132])).

fof(f132,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f403,plain,
    ( ~ l1_lattices(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl8_11
  <=> ~ l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f407,plain,
    ( ~ spl8_11
    | spl8_12 ),
    inference(avatar_split_clause,[],[f397,f405,f402])).

fof(f397,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_lattices(sK0)
      | m1_subset_1(k2_lattices(sK0,X1,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f171,f118])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t53_lattices.p',dt_k2_lattices)).
%------------------------------------------------------------------------------
