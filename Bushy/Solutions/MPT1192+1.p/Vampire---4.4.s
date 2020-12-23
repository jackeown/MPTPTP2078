%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattices__t17_lattices.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:00 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  338 ( 875 expanded)
%              Number of leaves         :   94 ( 362 expanded)
%              Depth                    :   13
%              Number of atoms          :  978 (2401 expanded)
%              Number of equality atoms :   65 ( 141 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1047,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f150,f157,f164,f171,f178,f185,f192,f199,f210,f217,f224,f231,f244,f251,f258,f265,f272,f279,f286,f312,f330,f337,f372,f391,f398,f416,f422,f429,f481,f492,f502,f511,f520,f530,f580,f590,f613,f622,f634,f646,f653,f660,f666,f669,f671,f673,f675,f676,f699,f706,f717,f734,f753,f768,f792,f799,f810,f824,f835,f858,f865,f998,f1039])).

fof(f1039,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_18
    | spl10_39
    | ~ spl10_106 ),
    inference(avatar_contradiction_clause,[],[f1038])).

fof(f1038,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_39
    | ~ spl10_106 ),
    inference(subsumption_resolution,[],[f1035,f285])).

fof(f285,plain,
    ( k1_lattices(sK0,sK1,sK1) != sK1
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl10_39
  <=> k1_lattices(sK0,sK1,sK1) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f1035,plain,
    ( k1_lattices(sK0,sK1,sK1) = sK1
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_106 ),
    inference(backward_demodulation,[],[f1034,f913])).

fof(f913,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1),sK1) = sK1
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_106 ),
    inference(forward_demodulation,[],[f870,f885])).

fof(f885,plain,
    ( k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_106 ),
    inference(unit_resulting_resolution,[],[f142,f149,f209,f198,f857,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',redefinition_k4_lattices)).

fof(f857,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl10_106 ),
    inference(avatar_component_clause,[],[f856])).

fof(f856,plain,
    ( spl10_106
  <=> m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f198,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl10_16
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f209,plain,
    ( l1_lattices(sK0)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl10_18
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f149,plain,
    ( v6_lattices(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl10_2
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f142,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f870,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1),sK1) = sK1
    | ~ spl10_1
    | ~ spl10_4
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_106 ),
    inference(unit_resulting_resolution,[],[f142,f170,f156,f198,f857,f111])).

fof(f111,plain,(
    ! [X4,X0,X3] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( k1_lattices(X0,k2_lattices(X0,sK2(X0),sK3(X0)),sK3(X0)) != sK3(X0)
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f78,f80,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK2(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k1_lattices(X0,k2_lattices(X0,X1,sK3(X0)),sK3(X0)) != sK3(X0)
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',d8_lattices)).

fof(f156,plain,
    ( v8_lattices(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl10_4
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f170,plain,
    ( l3_lattices(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl10_8
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f1034,plain,
    ( k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = sK1
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_106 ),
    inference(forward_demodulation,[],[f1007,f907])).

fof(f907,plain,
    ( k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = sK1
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_106 ),
    inference(forward_demodulation,[],[f888,f814])).

fof(f814,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = sK1
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_16 ),
    inference(unit_resulting_resolution,[],[f142,f170,f163,f198,f198,f115])).

fof(f115,plain,(
    ! [X4,X0,X3] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),sK5(X0))) != sK4(X0)
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f83,f85,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK4(X0),k1_lattices(X0,sK4(X0),X2)) != sK4(X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,X1,k1_lattices(X0,X1,sK5(X0))) != X1
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',d9_lattices)).

fof(f163,plain,
    ( v9_lattices(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl10_6
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f888,plain,
    ( k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_106 ),
    inference(unit_resulting_resolution,[],[f142,f149,f209,f198,f857,f126])).

fof(f1007,plain,
    ( k4_lattices(sK0,k1_lattices(sK0,sK1,sK1),sK1) = k4_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_106 ),
    inference(unit_resulting_resolution,[],[f142,f149,f209,f857,f198,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',commutativity_k4_lattices)).

fof(f998,plain,
    ( ~ spl10_111
    | spl10_45
    | ~ spl10_106 ),
    inference(avatar_split_clause,[],[f902,f856,f307,f996])).

fof(f996,plain,
    ( spl10_111
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_lattices(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_111])])).

fof(f307,plain,
    ( spl10_45
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f902,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_lattices(sK0,sK1,sK1))
    | ~ spl10_45
    | ~ spl10_106 ),
    inference(unit_resulting_resolution,[],[f308,f857,f288])).

fof(f288,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f122,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',antisymmetry_r2_hidden)).

fof(f122,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',t2_subset)).

fof(f308,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_45 ),
    inference(avatar_component_clause,[],[f307])).

fof(f865,plain,
    ( spl10_108
    | spl10_1
    | ~ spl10_2
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f760,f208,f197,f148,f141,f863])).

fof(f863,plain,
    ( spl10_108
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_108])])).

fof(f760,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(unit_resulting_resolution,[],[f142,f149,f209,f198,f198,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',dt_k4_lattices)).

fof(f858,plain,
    ( spl10_106
    | spl10_1
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f715,f215,f197,f141,f856])).

fof(f215,plain,
    ( spl10_20
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f715,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_16
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f142,f216,f198,f198,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',dt_k1_lattices)).

fof(f216,plain,
    ( l2_lattices(sK0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f215])).

fof(f835,plain,
    ( ~ spl10_105
    | spl10_101 ),
    inference(avatar_split_clause,[],[f826,f808,f833])).

fof(f833,plain,
    ( spl10_105
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_105])])).

fof(f808,plain,
    ( spl10_101
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_101])])).

fof(f826,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl10_101 ),
    inference(unit_resulting_resolution,[],[f809,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',t1_subset)).

fof(f809,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl10_101 ),
    inference(avatar_component_clause,[],[f808])).

fof(f824,plain,
    ( ~ spl10_103
    | spl10_97 ),
    inference(avatar_split_clause,[],[f801,f790,f822])).

fof(f822,plain,
    ( spl10_103
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_103])])).

fof(f790,plain,
    ( spl10_97
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f801,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_97 ),
    inference(unit_resulting_resolution,[],[f791,f121])).

fof(f791,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_97 ),
    inference(avatar_component_clause,[],[f790])).

fof(f810,plain,
    ( ~ spl10_101
    | ~ spl10_64
    | spl10_79 ),
    inference(avatar_split_clause,[],[f743,f632,f506,f808])).

fof(f506,plain,
    ( spl10_64
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f632,plain,
    ( spl10_79
  <=> ~ m1_subset_1(sK1,sK6(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f743,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK6(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl10_64
    | ~ spl10_79 ),
    inference(unit_resulting_resolution,[],[f507,f633,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',t4_subset)).

fof(f633,plain,
    ( ~ m1_subset_1(sK1,sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_79 ),
    inference(avatar_component_clause,[],[f632])).

fof(f507,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f506])).

fof(f799,plain,
    ( ~ spl10_99
    | spl10_59 ),
    inference(avatar_split_clause,[],[f483,f479,f797])).

fof(f797,plain,
    ( spl10_99
  <=> ~ r2_hidden(sK1,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f479,plain,
    ( spl10_59
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f483,plain,
    ( ~ r2_hidden(sK1,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl10_59 ),
    inference(unit_resulting_resolution,[],[f119,f480,f130])).

fof(f480,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_59 ),
    inference(avatar_component_clause,[],[f479])).

fof(f119,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',existence_m1_subset_1)).

fof(f792,plain,
    ( ~ spl10_97
    | ~ spl10_54
    | spl10_59 ),
    inference(avatar_split_clause,[],[f482,f479,f396,f790])).

fof(f396,plain,
    ( spl10_54
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f482,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_54
    | ~ spl10_59 ),
    inference(unit_resulting_resolution,[],[f397,f480,f130])).

fof(f397,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f396])).

fof(f768,plain,
    ( ~ spl10_95
    | spl10_93 ),
    inference(avatar_split_clause,[],[f755,f751,f766])).

fof(f766,plain,
    ( spl10_95
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_95])])).

fof(f751,plain,
    ( spl10_93
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f755,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f752,f121])).

fof(f752,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_93 ),
    inference(avatar_component_clause,[],[f751])).

fof(f753,plain,
    ( ~ spl10_93
    | spl10_59
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f688,f506,f479,f751])).

fof(f688,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_59
    | ~ spl10_64 ),
    inference(unit_resulting_resolution,[],[f480,f507,f130])).

fof(f734,plain,
    ( ~ spl10_91
    | spl10_87 ),
    inference(avatar_split_clause,[],[f707,f697,f732])).

fof(f732,plain,
    ( spl10_91
  <=> ~ r2_hidden(k1_xboole_0,sK6(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).

fof(f697,plain,
    ( spl10_87
  <=> ~ m1_subset_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).

fof(f707,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(k1_zfmisc_1(sK1)))
    | ~ spl10_87 ),
    inference(unit_resulting_resolution,[],[f119,f698,f130])).

fof(f698,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ spl10_87 ),
    inference(avatar_component_clause,[],[f697])).

fof(f717,plain,
    ( ~ spl10_45
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f468,f396,f307])).

fof(f468,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_54 ),
    inference(unit_resulting_resolution,[],[f397,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',t7_boole)).

fof(f706,plain,
    ( ~ spl10_89
    | spl10_51
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f681,f427,f367,f704])).

fof(f704,plain,
    ( spl10_89
  <=> ~ r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f367,plain,
    ( spl10_51
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f427,plain,
    ( spl10_56
  <=> m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f681,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl10_51
    | ~ spl10_56 ),
    inference(unit_resulting_resolution,[],[f368,f428,f288])).

fof(f428,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f427])).

fof(f368,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f367])).

fof(f699,plain,
    ( ~ spl10_87
    | spl10_43
    | spl10_51
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f680,f427,f367,f301,f697])).

fof(f301,plain,
    ( spl10_43
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f680,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ spl10_43
    | ~ spl10_51
    | ~ spl10_56 ),
    inference(unit_resulting_resolution,[],[f368,f302,f428,f289])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f288,f122])).

fof(f302,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f301])).

fof(f676,plain,
    ( ~ spl10_51
    | ~ spl10_68 ),
    inference(avatar_split_clause,[],[f601,f528,f367])).

fof(f528,plain,
    ( spl10_68
  <=> r2_hidden(sK6(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f601,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_68 ),
    inference(unit_resulting_resolution,[],[f529,f124])).

fof(f529,plain,
    ( r2_hidden(sK6(k1_xboole_0),k1_xboole_0)
    | ~ spl10_68 ),
    inference(avatar_component_clause,[],[f528])).

fof(f675,plain,
    ( ~ spl10_44
    | ~ spl10_54 ),
    inference(avatar_contradiction_clause,[],[f674])).

fof(f674,plain,
    ( $false
    | ~ spl10_44
    | ~ spl10_54 ),
    inference(subsumption_resolution,[],[f311,f468])).

fof(f311,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl10_44
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f673,plain,
    ( ~ spl10_50
    | ~ spl10_68 ),
    inference(avatar_contradiction_clause,[],[f672])).

fof(f672,plain,
    ( $false
    | ~ spl10_50
    | ~ spl10_68 ),
    inference(subsumption_resolution,[],[f371,f601])).

fof(f371,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl10_50
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f671,plain,
    ( ~ spl10_56
    | spl10_65
    | ~ spl10_68 ),
    inference(avatar_contradiction_clause,[],[f670])).

fof(f670,plain,
    ( $false
    | ~ spl10_56
    | ~ spl10_65
    | ~ spl10_68 ),
    inference(subsumption_resolution,[],[f428,f661])).

fof(f661,plain,
    ( ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl10_65
    | ~ spl10_68 ),
    inference(subsumption_resolution,[],[f513,f601])).

fof(f513,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl10_65 ),
    inference(resolution,[],[f510,f122])).

fof(f510,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl10_65 ),
    inference(avatar_component_clause,[],[f509])).

fof(f509,plain,
    ( spl10_65
  <=> ~ r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f669,plain,
    ( ~ spl10_62
    | ~ spl10_68
    | ~ spl10_72 ),
    inference(avatar_contradiction_clause,[],[f668])).

fof(f668,plain,
    ( $false
    | ~ spl10_62
    | ~ spl10_68
    | ~ spl10_72 ),
    inference(subsumption_resolution,[],[f667,f601])).

fof(f667,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_62
    | ~ spl10_72 ),
    inference(forward_demodulation,[],[f501,f589])).

fof(f589,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f588])).

fof(f588,plain,
    ( spl10_72
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f501,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl10_62
  <=> v1_xboole_0(sK6(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f666,plain,
    ( spl10_65
    | ~ spl10_68
    | ~ spl10_72
    | ~ spl10_78 ),
    inference(avatar_contradiction_clause,[],[f665])).

fof(f665,plain,
    ( $false
    | ~ spl10_65
    | ~ spl10_68
    | ~ spl10_72
    | ~ spl10_78 ),
    inference(subsumption_resolution,[],[f664,f661])).

fof(f664,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl10_72
    | ~ spl10_78 ),
    inference(backward_demodulation,[],[f589,f630])).

fof(f630,plain,
    ( m1_subset_1(sK1,sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_78 ),
    inference(avatar_component_clause,[],[f629])).

fof(f629,plain,
    ( spl10_78
  <=> m1_subset_1(sK1,sK6(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f660,plain,
    ( spl10_84
    | spl10_45 ),
    inference(avatar_split_clause,[],[f443,f307,f658])).

fof(f658,plain,
    ( spl10_84
  <=> r2_hidden(sK6(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f443,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f119,f308,f122])).

fof(f653,plain,
    ( ~ spl10_83
    | spl10_45 ),
    inference(avatar_split_clause,[],[f442,f307,f651])).

fof(f651,plain,
    ( spl10_83
  <=> ~ r2_hidden(u1_struct_0(sK0),sK6(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_83])])).

fof(f442,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(u1_struct_0(sK0)))
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f119,f308,f288])).

fof(f646,plain,
    ( ~ spl10_81
    | spl10_41 ),
    inference(avatar_split_clause,[],[f321,f298,f644])).

fof(f644,plain,
    ( spl10_81
  <=> ~ r2_hidden(u1_struct_0(sK0),sK6(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).

fof(f298,plain,
    ( spl10_41
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f321,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK6(k1_zfmisc_1(sK1)))
    | ~ spl10_41 ),
    inference(unit_resulting_resolution,[],[f119,f299,f130])).

fof(f299,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f298])).

fof(f634,plain,
    ( ~ spl10_79
    | spl10_63
    | spl10_75 ),
    inference(avatar_split_clause,[],[f614,f611,f497,f632])).

fof(f497,plain,
    ( spl10_63
  <=> ~ v1_xboole_0(sK6(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).

fof(f611,plain,
    ( spl10_75
  <=> ~ r2_hidden(sK1,sK6(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f614,plain,
    ( ~ m1_subset_1(sK1,sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_63
    | ~ spl10_75 ),
    inference(unit_resulting_resolution,[],[f498,f612,f122])).

fof(f612,plain,
    ( ~ r2_hidden(sK1,sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_75 ),
    inference(avatar_component_clause,[],[f611])).

fof(f498,plain,
    ( ~ v1_xboole_0(sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_63 ),
    inference(avatar_component_clause,[],[f497])).

fof(f622,plain,
    ( ~ spl10_77
    | spl10_71 ),
    inference(avatar_split_clause,[],[f582,f578,f620])).

fof(f620,plain,
    ( spl10_77
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f578,plain,
    ( spl10_71
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_71])])).

fof(f582,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_71 ),
    inference(unit_resulting_resolution,[],[f579,f121])).

fof(f579,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_71 ),
    inference(avatar_component_clause,[],[f578])).

fof(f613,plain,
    ( ~ spl10_75
    | spl10_57 ),
    inference(avatar_split_clause,[],[f439,f424,f611])).

fof(f424,plain,
    ( spl10_57
  <=> ~ m1_subset_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f439,plain,
    ( ~ r2_hidden(sK1,sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_57 ),
    inference(unit_resulting_resolution,[],[f119,f425,f130])).

fof(f425,plain,
    ( ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl10_57 ),
    inference(avatar_component_clause,[],[f424])).

fof(f590,plain,
    ( spl10_72
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f558,f500,f588])).

fof(f558,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_62 ),
    inference(unit_resulting_resolution,[],[f501,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',t6_boole)).

fof(f580,plain,
    ( ~ spl10_71
    | ~ spl10_54
    | spl10_57 ),
    inference(avatar_split_clause,[],[f469,f424,f396,f578])).

fof(f469,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_54
    | ~ spl10_57 ),
    inference(unit_resulting_resolution,[],[f425,f397,f130])).

fof(f530,plain,
    ( spl10_68
    | spl10_51 ),
    inference(avatar_split_clause,[],[f504,f367,f528])).

fof(f504,plain,
    ( r2_hidden(sK6(k1_xboole_0),k1_xboole_0)
    | ~ spl10_51 ),
    inference(unit_resulting_resolution,[],[f119,f368,f122])).

fof(f520,plain,
    ( ~ spl10_67
    | spl10_51 ),
    inference(avatar_split_clause,[],[f503,f367,f518])).

fof(f518,plain,
    ( spl10_67
  <=> ~ r2_hidden(k1_xboole_0,sK6(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f503,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(k1_xboole_0))
    | ~ spl10_51 ),
    inference(unit_resulting_resolution,[],[f119,f368,f288])).

fof(f511,plain,
    ( ~ spl10_65
    | spl10_57 ),
    inference(avatar_split_clause,[],[f440,f424,f509])).

fof(f440,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | ~ spl10_57 ),
    inference(unit_resulting_resolution,[],[f425,f121])).

fof(f502,plain,
    ( spl10_62
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f494,f370,f500])).

fof(f494,plain,
    ( v1_xboole_0(sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_50 ),
    inference(unit_resulting_resolution,[],[f119,f430,f122])).

fof(f430,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_50 ),
    inference(unit_resulting_resolution,[],[f119,f371,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',t5_subset)).

fof(f492,plain,
    ( ~ spl10_61
    | spl10_59 ),
    inference(avatar_split_clause,[],[f484,f479,f490])).

fof(f490,plain,
    ( spl10_61
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f484,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_59 ),
    inference(unit_resulting_resolution,[],[f480,f121])).

fof(f481,plain,
    ( ~ spl10_59
    | ~ spl10_48
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f459,f370,f335,f479])).

fof(f335,plain,
    ( spl10_48
  <=> r2_hidden(sK6(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f459,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_48
    | ~ spl10_50 ),
    inference(unit_resulting_resolution,[],[f371,f336,f131])).

fof(f336,plain,
    ( r2_hidden(sK6(sK1),sK1)
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f335])).

fof(f429,plain,
    ( spl10_56
    | ~ spl10_16
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f408,f310,f197,f427])).

fof(f408,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl10_16
    | ~ spl10_44 ),
    inference(backward_demodulation,[],[f403,f198])).

fof(f403,plain,
    ( u1_struct_0(sK0) = k1_xboole_0
    | ~ spl10_44 ),
    inference(unit_resulting_resolution,[],[f311,f102])).

fof(f422,plain,
    ( spl10_50
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f410,f310,f370])).

fof(f410,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_44 ),
    inference(backward_demodulation,[],[f403,f311])).

fof(f416,plain,
    ( ~ spl10_44
    | spl10_51 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | ~ spl10_44
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f410,f368])).

fof(f398,plain,
    ( spl10_54
    | ~ spl10_16
    | spl10_45 ),
    inference(avatar_split_clause,[],[f319,f307,f197,f396])).

fof(f319,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl10_16
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f198,f308,f122])).

fof(f391,plain,
    ( ~ spl10_53
    | ~ spl10_16
    | spl10_45 ),
    inference(avatar_split_clause,[],[f317,f307,f197,f389])).

fof(f389,plain,
    ( spl10_53
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f317,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl10_16
    | ~ spl10_45 ),
    inference(unit_resulting_resolution,[],[f198,f308,f288])).

fof(f372,plain,
    ( spl10_50
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f352,f304,f370])).

fof(f304,plain,
    ( spl10_42
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f352,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_42 ),
    inference(backward_demodulation,[],[f344,f305])).

fof(f305,plain,
    ( v1_xboole_0(sK1)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f304])).

fof(f344,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_42 ),
    inference(unit_resulting_resolution,[],[f305,f102])).

fof(f337,plain,
    ( spl10_48
    | spl10_43 ),
    inference(avatar_split_clause,[],[f314,f301,f335])).

fof(f314,plain,
    ( r2_hidden(sK6(sK1),sK1)
    | ~ spl10_43 ),
    inference(unit_resulting_resolution,[],[f119,f302,f122])).

fof(f330,plain,
    ( ~ spl10_47
    | spl10_43 ),
    inference(avatar_split_clause,[],[f313,f301,f328])).

fof(f328,plain,
    ( spl10_47
  <=> ~ r2_hidden(sK1,sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f313,plain,
    ( ~ r2_hidden(sK1,sK6(sK1))
    | ~ spl10_43 ),
    inference(unit_resulting_resolution,[],[f119,f302,f288])).

fof(f312,plain,
    ( ~ spl10_41
    | spl10_42
    | spl10_44
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f290,f197,f310,f304,f298])).

fof(f290,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl10_16 ),
    inference(resolution,[],[f289,f198])).

fof(f286,plain,(
    ~ spl10_39 ),
    inference(avatar_split_clause,[],[f101,f284])).

fof(f101,plain,(
    k1_lattices(sK0,sK1,sK1) != sK1 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( k1_lattices(sK0,sK1,sK1) != sK1
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v9_lattices(sK0)
    & v8_lattices(sK0)
    & v6_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f42,f75,f74])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_lattices(X0,X1,X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_lattices(sK0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v9_lattices(sK0)
      & v8_lattices(sK0)
      & v6_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( k1_lattices(X0,sK1,sK1) != sK1
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_lattices(X0,X1,X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v9_lattices(X0)
      & v8_lattices(X0)
      & v6_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k1_lattices(X0,X1,X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',t17_lattices)).

fof(f279,plain,
    ( spl10_36
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f237,f222,f277])).

fof(f277,plain,
    ( spl10_36
  <=> v1_funct_1(u1_lattices(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f222,plain,
    ( spl10_22
  <=> l1_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f237,plain,
    ( v1_funct_1(u1_lattices(sK7))
    | ~ spl10_22 ),
    inference(unit_resulting_resolution,[],[f223,f108])).

fof(f108,plain,(
    ! [X0] :
      ( v1_funct_1(u1_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',dt_u1_lattices)).

fof(f223,plain,
    ( l1_lattices(sK7)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f222])).

fof(f272,plain,
    ( spl10_34
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f234,f229,f270])).

fof(f270,plain,
    ( spl10_34
  <=> v1_funct_1(u2_lattices(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f229,plain,
    ( spl10_24
  <=> l2_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f234,plain,
    ( v1_funct_1(u2_lattices(sK7))
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f230,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',dt_u2_lattices)).

fof(f230,plain,
    ( l2_lattices(sK7)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f229])).

fof(f265,plain,
    ( spl10_32
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f236,f208,f263])).

fof(f263,plain,
    ( spl10_32
  <=> v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f236,plain,
    ( v1_funct_1(u1_lattices(sK0))
    | ~ spl10_18 ),
    inference(unit_resulting_resolution,[],[f209,f108])).

fof(f258,plain,
    ( spl10_30
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f233,f215,f256])).

fof(f256,plain,
    ( spl10_30
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f233,plain,
    ( v1_funct_1(u2_lattices(sK0))
    | ~ spl10_20 ),
    inference(unit_resulting_resolution,[],[f216,f105])).

fof(f251,plain,
    ( spl10_28
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f235,f190,f249])).

fof(f249,plain,
    ( spl10_28
  <=> v1_funct_1(u1_lattices(sK9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f190,plain,
    ( spl10_14
  <=> l1_lattices(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f235,plain,
    ( v1_funct_1(u1_lattices(sK9))
    | ~ spl10_14 ),
    inference(unit_resulting_resolution,[],[f191,f108])).

fof(f191,plain,
    ( l1_lattices(sK9)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f190])).

fof(f244,plain,
    ( spl10_26
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f232,f183,f242])).

fof(f242,plain,
    ( spl10_26
  <=> v1_funct_1(u2_lattices(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f183,plain,
    ( spl10_12
  <=> l2_lattices(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f232,plain,
    ( v1_funct_1(u2_lattices(sK8))
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f184,f105])).

fof(f184,plain,
    ( l2_lattices(sK8)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f183])).

fof(f231,plain,
    ( spl10_24
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f203,f176,f229])).

fof(f176,plain,
    ( spl10_10
  <=> l3_lattices(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f203,plain,
    ( l2_lattices(sK7)
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f177,f104])).

fof(f104,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',dt_l3_lattices)).

fof(f177,plain,
    ( l3_lattices(sK7)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f224,plain,
    ( spl10_22
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f201,f176,f222])).

fof(f201,plain,
    ( l1_lattices(sK7)
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f177,f103])).

fof(f103,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f217,plain,
    ( spl10_20
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f202,f169,f215])).

fof(f202,plain,
    ( l2_lattices(sK0)
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f170,f104])).

fof(f210,plain,
    ( spl10_18
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f200,f169,f208])).

fof(f200,plain,
    ( l1_lattices(sK0)
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f170,f103])).

fof(f199,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f100,f197])).

fof(f100,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f192,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f136,f190])).

fof(f136,plain,(
    l1_lattices(sK9) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    l1_lattices(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f23,f93])).

fof(f93,plain,
    ( ? [X0] : l1_lattices(X0)
   => l1_lattices(sK9) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ? [X0] : l1_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',existence_l1_lattices)).

fof(f185,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f135,f183])).

fof(f135,plain,(
    l2_lattices(sK8) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    l2_lattices(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f91])).

fof(f91,plain,
    ( ? [X0] : l2_lattices(X0)
   => l2_lattices(sK8) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ? [X0] : l2_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',existence_l2_lattices)).

fof(f178,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f134,f176])).

fof(f134,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    l3_lattices(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f89])).

fof(f89,plain,
    ( ? [X0] : l3_lattices(X0)
   => l3_lattices(sK7) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ? [X0] : l3_lattices(X0) ),
    file('/export/starexec/sandbox/benchmark/lattices__t17_lattices.p',existence_l3_lattices)).

fof(f171,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f99,f169])).

fof(f99,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f164,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f98,f162])).

fof(f98,plain,(
    v9_lattices(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f157,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f97,f155])).

fof(f97,plain,(
    v8_lattices(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f150,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f96,f148])).

fof(f96,plain,(
    v6_lattices(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f143,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f95,f141])).

fof(f95,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).
%------------------------------------------------------------------------------
