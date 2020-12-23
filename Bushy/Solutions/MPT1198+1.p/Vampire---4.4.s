%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t25_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:01 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  298 (3055 expanded)
%              Number of leaves         :   59 (1300 expanded)
%              Depth                    :   22
%              Number of atoms          : 1568 (14412 expanded)
%              Number of equality atoms :  116 (1867 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5298,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f115,f122,f129,f136,f143,f150,f157,f164,f171,f180,f187,f225,f232,f244,f253,f261,f284,f291,f298,f305,f312,f325,f332,f341,f353,f361,f368,f611,f618,f625,f632,f883,f890,f897,f904,f911,f2378,f2574,f3019,f3691,f3833,f3891])).

fof(f3891,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | spl9_51
    | ~ spl9_52 ),
    inference(avatar_contradiction_clause,[],[f3890])).

fof(f3890,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_51
    | ~ spl9_52 ),
    inference(subsumption_resolution,[],[f3889,f352])).

fof(f352,plain,
    ( k1_lattices(sK0,sK1,sK3) != sK3
    | ~ spl9_51 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl9_51
  <=> k1_lattices(sK0,sK1,sK3) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f3889,plain,
    ( k1_lattices(sK0,sK1,sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f3888,f3062])).

fof(f3062,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK3)) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f3059,f2719])).

fof(f2719,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK1)),sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2699,f331])).

fof(f331,plain,
    ( k1_lattices(sK0,sK2,sK3) = sK3
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl9_46
  <=> k1_lattices(sK0,sK2,sK3) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f2699,plain,
    ( k1_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK1)),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f2692,f2515])).

fof(f2515,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK1)),sK3) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34 ),
    inference(forward_demodulation,[],[f2009,f2085])).

fof(f2085,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK3) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f135,f135,f149,f83])).

fof(f83,plain,(
    ! [X6,X4,X0,X5] :
      ( ~ v5_lattices(X0)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ( k1_lattices(X0,k1_lattices(X0,sK4(X0),sK5(X0)),sK6(X0)) != k1_lattices(X0,sK4(X0),k1_lattices(X0,sK5(X0),sK6(X0)))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f60,f63,f62,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_lattices(X0,k1_lattices(X0,sK4(X0),X2),X3) != k1_lattices(X0,sK4(X0),k1_lattices(X0,X2,X3))
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( k1_lattices(X0,X1,k1_lattices(X0,sK5(X0),X3)) != k1_lattices(X0,k1_lattices(X0,X1,sK5(X0)),X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_lattices(X0,X1,k1_lattices(X0,X2,sK6(X0))) != k1_lattices(X0,k1_lattices(X0,X1,X2),sK6(X0))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ! [X6] :
                      ( k1_lattices(X0,X4,k1_lattices(X0,X5,X6)) = k1_lattices(X0,k1_lattices(X0,X4,X5),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v5_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ? [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) != k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ! [X3] :
                      ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v5_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v5_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k1_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k1_lattices(X0,X1,X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',d5_lattices)).

fof(f149,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl9_12
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f135,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl9_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f114,plain,
    ( v5_lattices(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl9_2
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f121,plain,
    ( l2_lattices(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_4
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f107,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f2009,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK1)),sK3) = k1_lattices(sK0,sK2,k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f142,f283,f149,f83])).

fof(f283,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl9_34
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f142,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl9_10
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f2692,plain,
    ( k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2689,f2367])).

fof(f2367,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2366,f331])).

fof(f2366,plain,
    ( k1_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2097,f331])).

fof(f2097,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK3) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f142,f142,f149,f83])).

fof(f2689,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK3) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f2685,f2490])).

fof(f2490,plain,
    ( k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),k1_lattices(sK0,sK2,sK2)),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_42
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2489,f2085])).

fof(f2489,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK3) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),k1_lattices(sK0,sK2,sK2)),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_42
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2034,f2367])).

fof(f2034,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),k1_lattices(sK0,sK2,sK2)),sK3) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f283,f311,f149,f83])).

fof(f311,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl9_42
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f2685,plain,
    ( k1_lattices(sK0,sK2,sK2) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),k1_lattices(sK0,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_34
    | ~ spl9_44 ),
    inference(backward_demodulation,[],[f2684,f1968])).

fof(f1968,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2),sK2) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),k1_lattices(sK0,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f283,f142,f142,f83])).

fof(f2684,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2) = sK2
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f2683,f324])).

fof(f324,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl9_44
  <=> k1_lattices(sK0,sK1,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f2683,plain,
    ( k1_lattices(sK0,sK1,sK2) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1964,f324])).

fof(f1964,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f135,f135,f142,f83])).

fof(f3059,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK1)),sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36 ),
    inference(backward_demodulation,[],[f1844,f2079])).

fof(f2079,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1),sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_36 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f290,f135,f149,f83])).

fof(f290,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl9_36
  <=> m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f1844,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK1) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f142,f135,f135,f83])).

fof(f3888,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f3887,f3012])).

fof(f3012,plain,
    ( k1_lattices(sK0,sK2,sK1) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1854,f324])).

fof(f1854,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),sK1) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f135,f142,f135,f83])).

fof(f3887,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_34
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f1535,f3062])).

fof(f1535,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK1,sK3)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_36
    | ~ spl9_52 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f135,f290,f360,f83])).

fof(f360,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl9_52
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f3833,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | spl9_51
    | ~ spl9_52 ),
    inference(avatar_contradiction_clause,[],[f3832])).

fof(f3832,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_51
    | ~ spl9_52 ),
    inference(subsumption_resolution,[],[f3831,f352])).

fof(f3831,plain,
    ( k1_lattices(sK0,sK1,sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f3830,f3006])).

fof(f3006,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),k1_lattices(sK0,sK1,sK3)) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f3003,f2668])).

fof(f2668,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)),sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2649,f331])).

fof(f2649,plain,
    ( k1_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f2642,f2504])).

fof(f2504,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)),sK3) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f2020,f2086])).

fof(f2086,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK3) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f142,f135,f149,f83])).

fof(f2020,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)),sK3) = k1_lattices(sK0,sK2,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f142,f290,f149,f83])).

fof(f2642,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2639,f2475])).

fof(f2475,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)),sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_42
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2474,f331])).

fof(f2474,plain,
    ( k1_lattices(sK0,sK2,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_42
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2042,f2367])).

fof(f2042,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)),sK3) = k1_lattices(sK0,sK2,k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f142,f311,f149,f83])).

fof(f2639,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f2638,f2488])).

fof(f2488,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,sK2)),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2487,f2086])).

fof(f2487,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK3) = k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,sK2)),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2035,f2367])).

fof(f2035,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,sK2)),sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f290,f311,f149,f83])).

fof(f2638,plain,
    ( k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2)) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_36
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f2634,f1976])).

fof(f1976,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK2) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f142,f142,f142,f83])).

fof(f2634,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK2) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_36
    | ~ spl9_44 ),
    inference(backward_demodulation,[],[f2633,f1969])).

fof(f1969,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2),sK2) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),k1_lattices(sK0,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_36 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f290,f142,f142,f83])).

fof(f2633,plain,
    ( k1_lattices(sK0,sK2,sK2) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1965,f324])).

fof(f1965,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK2) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f142,f135,f142,f83])).

fof(f3003,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1)),sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_42 ),
    inference(backward_demodulation,[],[f1855,f2081])).

fof(f2081,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK1),sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f311,f135,f149,f83])).

fof(f1855,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK1) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK2,sK1))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f142,f142,f135,f83])).

fof(f3830,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f3829,f2568])).

fof(f2568,plain,
    ( k1_lattices(sK0,sK2,sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f1975,f324])).

fof(f1975,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),sK2) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f135,f142,f142,f83])).

fof(f3829,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK2)),k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f1557,f3006])).

fof(f1557,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK2)),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),k1_lattices(sK0,sK1,sK3)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_42
    | ~ spl9_52 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f135,f311,f360,f83])).

fof(f3691,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | spl9_51
    | ~ spl9_52 ),
    inference(avatar_contradiction_clause,[],[f3690])).

fof(f3690,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_51
    | ~ spl9_52 ),
    inference(subsumption_resolution,[],[f3689,f352])).

fof(f3689,plain,
    ( k1_lattices(sK0,sK1,sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f3688,f2642])).

fof(f3688,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f3687,f324])).

fof(f3687,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_52 ),
    inference(forward_demodulation,[],[f1612,f2642])).

fof(f1612,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),k1_lattices(sK0,sK1,sK3)) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_52 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f135,f142,f360,f83])).

fof(f3019,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | spl9_51 ),
    inference(avatar_contradiction_clause,[],[f3018])).

fof(f3018,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_51 ),
    inference(subsumption_resolution,[],[f3017,f352])).

fof(f3017,plain,
    ( k1_lattices(sK0,sK1,sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f3014,f2644])).

fof(f2644,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f2642,f2086])).

fof(f3014,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f3012,f2650])).

fof(f2650,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f2642,f2505])).

fof(f2505,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),sK3) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,k1_lattices(sK0,sK1,sK3)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_36 ),
    inference(forward_demodulation,[],[f2019,f2086])).

fof(f2019,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK1)),sK3) = k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK1),sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_36 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f135,f290,f149,f83])).

fof(f2574,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | spl9_51 ),
    inference(avatar_contradiction_clause,[],[f2573])).

fof(f2573,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_51 ),
    inference(subsumption_resolution,[],[f2572,f352])).

fof(f2572,plain,
    ( k1_lattices(sK0,sK1,sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2569,f2367])).

fof(f2569,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_42
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f2568,f2476])).

fof(f2476,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK2)),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_42
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2041,f2367])).

fof(f2041,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK2)),sK3) = k1_lattices(sK0,sK1,k1_lattices(sK0,k1_lattices(sK0,sK2,sK2),sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_42 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f135,f311,f149,f83])).

fof(f2378,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_44
    | ~ spl9_46
    | spl9_51 ),
    inference(avatar_contradiction_clause,[],[f2377])).

fof(f2377,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_44
    | ~ spl9_46
    | ~ spl9_51 ),
    inference(subsumption_resolution,[],[f2376,f352])).

fof(f2376,plain,
    ( k1_lattices(sK0,sK1,sK3) = sK3
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2375,f331])).

fof(f2375,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2374,f324])).

fof(f2374,plain,
    ( k1_lattices(sK0,sK1,sK3) = k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),sK3)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_46 ),
    inference(forward_demodulation,[],[f2096,f331])).

fof(f2096,plain,
    ( k1_lattices(sK0,k1_lattices(sK0,sK1,sK2),sK3) = k1_lattices(sK0,sK1,k1_lattices(sK0,sK2,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f107,f121,f114,f135,f142,f149,f83])).

fof(f911,plain,
    ( spl9_72
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f780,f242,f223,f178,f141,f909])).

fof(f909,plain,
    ( spl9_72
  <=> m1_subset_1(k1_binop_1(u2_lattices(sK0),sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f178,plain,
    ( spl9_20
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f223,plain,
    ( spl9_24
  <=> v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f242,plain,
    ( spl9_28
  <=> m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f780,plain,
    ( m1_subset_1(k1_binop_1(u2_lattices(sK0),sK2,sK2),u1_struct_0(sK0))
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(backward_demodulation,[],[f729,f536])).

fof(f536,plain,
    ( m1_subset_1(k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK2,sK2),u1_struct_0(sK0))
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f179,f142,f142,f224,f243,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',dt_k4_binop_1)).

fof(f243,plain,
    ( m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f242])).

fof(f224,plain,
    ( v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f223])).

fof(f179,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f178])).

fof(f729,plain,
    ( k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK2,sK2) = k1_binop_1(u2_lattices(sK0),sK2,sK2)
    | ~ spl9_10
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f179,f142,f142,f224,f243,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',redefinition_k4_binop_1)).

fof(f904,plain,
    ( spl9_70
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f779,f242,f223,f178,f148,f141,f902])).

fof(f902,plain,
    ( spl9_70
  <=> m1_subset_1(k1_binop_1(u2_lattices(sK0),sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f779,plain,
    ( m1_subset_1(k1_binop_1(u2_lattices(sK0),sK3,sK2),u1_struct_0(sK0))
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(backward_demodulation,[],[f730,f546])).

fof(f546,plain,
    ( m1_subset_1(k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK3,sK2),u1_struct_0(sK0))
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f179,f142,f149,f224,f243,f99])).

fof(f730,plain,
    ( k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK3,sK2) = k1_binop_1(u2_lattices(sK0),sK3,sK2)
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f179,f149,f142,f224,f243,f100])).

fof(f897,plain,
    ( spl9_68
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f770,f242,f223,f178,f148,f134,f895])).

fof(f895,plain,
    ( spl9_68
  <=> m1_subset_1(k1_binop_1(u2_lattices(sK0),sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f770,plain,
    ( m1_subset_1(k1_binop_1(u2_lattices(sK0),sK1,sK3),u1_struct_0(sK0))
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(backward_demodulation,[],[f739,f527])).

fof(f527,plain,
    ( m1_subset_1(k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK1,sK3),u1_struct_0(sK0))
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f179,f149,f135,f224,f243,f99])).

fof(f739,plain,
    ( k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK1,sK3) = k1_binop_1(u2_lattices(sK0),sK1,sK3)
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f179,f135,f149,f224,f243,f100])).

fof(f890,plain,
    ( spl9_66
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f769,f242,f223,f178,f148,f141,f888])).

fof(f888,plain,
    ( spl9_66
  <=> m1_subset_1(k1_binop_1(u2_lattices(sK0),sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f769,plain,
    ( m1_subset_1(k1_binop_1(u2_lattices(sK0),sK2,sK3),u1_struct_0(sK0))
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(backward_demodulation,[],[f740,f537])).

fof(f537,plain,
    ( m1_subset_1(k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK2,sK3),u1_struct_0(sK0))
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f179,f149,f142,f224,f243,f99])).

fof(f740,plain,
    ( k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK2,sK3) = k1_binop_1(u2_lattices(sK0),sK2,sK3)
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f179,f142,f149,f224,f243,f100])).

fof(f883,plain,
    ( spl9_64
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f768,f242,f223,f178,f148,f881])).

fof(f881,plain,
    ( spl9_64
  <=> m1_subset_1(k1_binop_1(u2_lattices(sK0),sK3,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f768,plain,
    ( m1_subset_1(k1_binop_1(u2_lattices(sK0),sK3,sK3),u1_struct_0(sK0))
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(backward_demodulation,[],[f741,f547])).

fof(f547,plain,
    ( m1_subset_1(k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK3,sK3),u1_struct_0(sK0))
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f179,f149,f149,f224,f243,f99])).

fof(f741,plain,
    ( k4_binop_1(u1_struct_0(sK0),u2_lattices(sK0),sK3,sK3) = k1_binop_1(u2_lattices(sK0),sK3,sK3)
    | ~ spl9_12
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f179,f149,f149,f224,f243,f100])).

fof(f632,plain,
    ( spl9_62
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f274,f134,f120,f106,f630])).

fof(f630,plain,
    ( spl9_62
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK7(u1_struct_0(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f274,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK7(u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f107,f121,f135,f90,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',dt_k1_lattices)).

fof(f90,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',existence_m1_subset_1)).

fof(f625,plain,
    ( spl9_60
    | spl9_1
    | ~ spl9_4
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f273,f148,f120,f106,f623])).

fof(f623,plain,
    ( spl9_60
  <=> m1_subset_1(k1_lattices(sK0,sK7(u1_struct_0(sK0)),sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f273,plain,
    ( m1_subset_1(k1_lattices(sK0,sK7(u1_struct_0(sK0)),sK3),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f107,f121,f90,f149,f96])).

fof(f618,plain,
    ( spl9_58
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f269,f141,f120,f106,f616])).

fof(f616,plain,
    ( spl9_58
  <=> m1_subset_1(k1_lattices(sK0,sK7(u1_struct_0(sK0)),sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f269,plain,
    ( m1_subset_1(k1_lattices(sK0,sK7(u1_struct_0(sK0)),sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f90,f142,f96])).

fof(f611,plain,
    ( spl9_56
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f265,f134,f120,f106,f609])).

fof(f609,plain,
    ( spl9_56
  <=> m1_subset_1(k1_lattices(sK0,sK7(u1_struct_0(sK0)),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f265,plain,
    ( m1_subset_1(k1_lattices(sK0,sK7(u1_struct_0(sK0)),sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f107,f121,f90,f135,f96])).

fof(f368,plain,
    ( spl9_54
    | spl9_1
    | ~ spl9_4
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f272,f148,f120,f106,f366])).

fof(f366,plain,
    ( spl9_54
  <=> m1_subset_1(k1_lattices(sK0,sK3,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f272,plain,
    ( m1_subset_1(k1_lattices(sK0,sK3,sK3),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f107,f121,f149,f149,f96])).

fof(f361,plain,
    ( spl9_52
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f270,f148,f134,f120,f106,f359])).

fof(f270,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f107,f121,f135,f149,f96])).

fof(f353,plain,
    ( ~ spl9_51
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12
    | spl9_19 ),
    inference(avatar_split_clause,[],[f342,f169,f148,f134,f120,f106,f351])).

fof(f169,plain,
    ( spl9_19
  <=> ~ r1_lattices(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f342,plain,
    ( k1_lattices(sK0,sK1,sK3) != sK3
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12
    | ~ spl9_19 ),
    inference(unit_resulting_resolution,[],[f107,f121,f170,f135,f149,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',d3_lattices)).

fof(f170,plain,
    ( ~ r1_lattices(sK0,sK1,sK3)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f169])).

fof(f341,plain,
    ( spl9_48
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f268,f148,f141,f120,f106,f339])).

fof(f339,plain,
    ( spl9_48
  <=> m1_subset_1(k1_lattices(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f268,plain,
    ( m1_subset_1(k1_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f107,f121,f149,f142,f96])).

fof(f332,plain,
    ( spl9_46
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f314,f162,f148,f141,f120,f106,f330])).

fof(f162,plain,
    ( spl9_16
  <=> r1_lattices(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f314,plain,
    ( k1_lattices(sK0,sK2,sK3) = sK3
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_16 ),
    inference(unit_resulting_resolution,[],[f107,f121,f142,f163,f149,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | k1_lattices(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f163,plain,
    ( r1_lattices(sK0,sK2,sK3)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f162])).

fof(f325,plain,
    ( spl9_44
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f313,f155,f141,f134,f120,f106,f323])).

fof(f155,plain,
    ( spl9_14
  <=> r1_lattices(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f313,plain,
    ( k1_lattices(sK0,sK1,sK2) = sK2
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f107,f121,f135,f156,f142,f88])).

fof(f156,plain,
    ( r1_lattices(sK0,sK1,sK2)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f312,plain,
    ( spl9_42
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f267,f141,f120,f106,f310])).

fof(f267,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f142,f142,f96])).

fof(f305,plain,
    ( spl9_40
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f266,f141,f134,f120,f106,f303])).

fof(f303,plain,
    ( spl9_40
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f266,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f135,f142,f96])).

fof(f298,plain,
    ( spl9_38
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f264,f148,f134,f120,f106,f296])).

fof(f296,plain,
    ( spl9_38
  <=> m1_subset_1(k1_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f264,plain,
    ( m1_subset_1(k1_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_12 ),
    inference(unit_resulting_resolution,[],[f107,f121,f149,f135,f96])).

fof(f291,plain,
    ( spl9_36
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f263,f141,f134,f120,f106,f289])).

fof(f263,plain,
    ( m1_subset_1(k1_lattices(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(unit_resulting_resolution,[],[f107,f121,f142,f135,f96])).

fof(f284,plain,
    ( spl9_34
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f262,f134,f120,f106,f282])).

fof(f262,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(unit_resulting_resolution,[],[f107,f121,f135,f135,f96])).

fof(f261,plain,
    ( spl9_32
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f236,f127,f259])).

fof(f259,plain,
    ( spl9_32
  <=> m1_subset_1(u2_lattices(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f127,plain,
    ( spl9_6
  <=> l2_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f236,plain,
    ( m1_subset_1(u2_lattices(sK8),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8))))
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f128,f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',dt_u2_lattices)).

fof(f128,plain,
    ( l2_lattices(sK8)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f127])).

fof(f253,plain,
    ( ~ spl9_31
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f245,f242,f251])).

fof(f251,plain,
    ( spl9_31
  <=> ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)),u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f245,plain,
    ( ~ r2_hidden(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)),u2_lattices(sK0))
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f243,f198])).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f197,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',t5_subset)).

fof(f197,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f196,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',t4_subset)).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f189,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',t2_subset)).

fof(f189,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f93,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',antisymmetry_r2_hidden)).

fof(f244,plain,
    ( spl9_28
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f235,f120,f242])).

fof(f235,plain,
    ( m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f121,f82])).

fof(f232,plain,
    ( spl9_26
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f218,f127,f230])).

fof(f230,plain,
    ( spl9_26
  <=> v1_funct_2(u2_lattices(sK8),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f218,plain,
    ( v1_funct_2(u2_lattices(sK8),k2_zfmisc_1(u1_struct_0(sK8),u1_struct_0(sK8)),u1_struct_0(sK8))
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f128,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f225,plain,
    ( spl9_24
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f217,f120,f223])).

fof(f217,plain,
    ( v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f121,f81])).

fof(f187,plain,
    ( spl9_22
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f173,f127,f185])).

fof(f185,plain,
    ( spl9_22
  <=> v1_funct_1(u2_lattices(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f173,plain,
    ( v1_funct_1(u2_lattices(sK8))
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f128,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f180,plain,
    ( spl9_20
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f172,f120,f178])).

fof(f172,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl9_4 ),
    inference(unit_resulting_resolution,[],[f121,f80])).

fof(f171,plain,(
    ~ spl9_19 ),
    inference(avatar_split_clause,[],[f78,f169])).

fof(f78,plain,(
    ~ r1_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ~ r1_lattices(sK0,sK1,sK3)
    & r1_lattices(sK0,sK2,sK3)
    & r1_lattices(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l2_lattices(sK0)
    & v5_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f57,f56,f55,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r1_lattices(X0,X2,X3)
                    & r1_lattices(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(sK0,X1,X3)
                  & r1_lattices(sK0,X2,X3)
                  & r1_lattices(sK0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l2_lattices(sK0)
      & v5_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_lattices(X0,sK1,X3)
                & r1_lattices(X0,X2,X3)
                & r1_lattices(X0,sK1,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_lattices(X0,X1,X3)
              & r1_lattices(X0,X2,X3)
              & r1_lattices(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r1_lattices(X0,sK2,X3)
            & r1_lattices(X0,X1,sK2)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r1_lattices(X0,X2,X3)
          & r1_lattices(X0,X1,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK3)
        & r1_lattices(X0,X2,sK3)
        & r1_lattices(X0,X1,X2)
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_lattices(X0,X1,X3)
                  & r1_lattices(X0,X2,X3)
                  & r1_lattices(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l2_lattices(X0)
      & v5_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l2_lattices(X0)
          & v5_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_lattices(X0,X2,X3)
                        & r1_lattices(X0,X1,X2) )
                     => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_lattices(X0,X2,X3)
                      & r1_lattices(X0,X1,X2) )
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',t25_lattices)).

fof(f164,plain,(
    spl9_16 ),
    inference(avatar_split_clause,[],[f77,f162])).

fof(f77,plain,(
    r1_lattices(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f157,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f76,f155])).

fof(f76,plain,(
    r1_lattices(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f150,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f75,f148])).

fof(f75,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f143,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f74,f141])).

fof(f74,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f136,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f73,f134])).

fof(f73,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f129,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f101,f127])).

fof(f101,plain,(
    l2_lattices(sK8) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    l2_lattices(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f18,f68])).

fof(f68,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK8) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t25_lattices.p',existence_l2_lattices)).

fof(f122,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f72,f120])).

fof(f72,plain,(
    l2_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f115,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f71,f113])).

fof(f71,plain,(
    v5_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f108,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f70,f106])).

fof(f70,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
