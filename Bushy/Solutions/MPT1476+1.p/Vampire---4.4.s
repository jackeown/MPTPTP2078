%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t9_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:59 EDT 2019

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 461 expanded)
%              Number of leaves         :   60 ( 197 expanded)
%              Depth                    :   10
%              Number of atoms          :  763 (1544 expanded)
%              Number of equality atoms :   89 ( 153 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f141,f169,f176,f246,f253,f273,f279,f295,f328,f352,f359,f366,f384,f393,f401,f465,f610,f615,f641,f651,f692,f783,f823,f830,f960,f976,f990,f1775,f1868,f1884,f2061,f2084,f2085,f2099,f2102,f2121,f2123])).

fof(f2123,plain,
    ( u1_orders_2(k7_lattice3(sK0)) != k4_relat_1(u1_orders_2(sK0))
    | u1_orders_2(sK0) != k4_relat_1(k4_relat_1(u1_orders_2(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0))))
    | ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    introduced(theory_axiom,[])).

fof(f2121,plain,
    ( spl9_85
    | ~ spl9_142
    | ~ spl9_144 ),
    inference(avatar_contradiction_clause,[],[f2118])).

fof(f2118,plain,
    ( $false
    | ~ spl9_85
    | ~ spl9_142
    | ~ spl9_144 ),
    inference(unit_resulting_resolution,[],[f966,f975,f606,f306])).

fof(f306,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f132,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',dt_k4_relat_1)).

fof(f132,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f77,f78])).

fof(f78,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',d7_relat_1)).

fof(f606,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_85 ),
    inference(avatar_component_clause,[],[f605])).

fof(f605,plain,
    ( spl9_85
  <=> ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f975,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0))))
    | ~ spl9_144 ),
    inference(avatar_component_clause,[],[f974])).

fof(f974,plain,
    ( spl9_144
  <=> r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_144])])).

fof(f966,plain,
    ( v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_142 ),
    inference(avatar_component_clause,[],[f965])).

fof(f965,plain,
    ( spl9_142
  <=> v1_relat_1(u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_142])])).

fof(f2102,plain,
    ( k8_lattice3(sK0,sK2) != sK2
    | k8_lattice3(sK0,sK1) != sK1
    | r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
    | ~ r1_orders_2(k7_lattice3(sK0),sK2,sK1) ),
    introduced(theory_axiom,[])).

fof(f2099,plain,
    ( ~ spl9_0
    | ~ spl9_8
    | ~ spl9_10
    | spl9_23
    | ~ spl9_120 ),
    inference(avatar_contradiction_clause,[],[f2098])).

fof(f2098,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_23
    | ~ spl9_120 ),
    inference(subsumption_resolution,[],[f2097,f140])).

fof(f140,plain,
    ( l1_orders_2(sK0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl9_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f2097,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_23
    | ~ spl9_120 ),
    inference(subsumption_resolution,[],[f2096,f168])).

fof(f168,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl9_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f2096,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_10
    | ~ spl9_23
    | ~ spl9_120 ),
    inference(subsumption_resolution,[],[f2095,f175])).

fof(f175,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl9_10
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f2095,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_23
    | ~ spl9_120 ),
    inference(subsumption_resolution,[],[f2087,f236])).

fof(f236,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl9_23
  <=> ~ r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f2087,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_120 ),
    inference(resolution,[],[f829,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',d9_orders_2)).

fof(f829,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl9_120 ),
    inference(avatar_component_clause,[],[f828])).

fof(f828,plain,
    ( spl9_120
  <=> r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).

fof(f2085,plain,
    ( u1_orders_2(k7_lattice3(sK0)) != k4_relat_1(u1_orders_2(sK0))
    | u1_orders_2(sK0) != k4_relat_1(k4_relat_1(u1_orders_2(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0)))) ),
    introduced(theory_axiom,[])).

fof(f2084,plain,
    ( spl9_260
    | ~ spl9_232
    | ~ spl9_234
    | ~ spl9_254 ),
    inference(avatar_split_clause,[],[f2069,f2035,f1882,f1866,f2082])).

fof(f2082,plain,
    ( spl9_260
  <=> u1_orders_2(k7_lattice3(sK0)) = k4_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_260])])).

fof(f1866,plain,
    ( spl9_232
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_232])])).

fof(f1882,plain,
    ( spl9_234
  <=> m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_234])])).

fof(f2035,plain,
    ( spl9_254
  <=> ! [X1,X0] :
        ( k7_lattice3(sK0) != g1_orders_2(X0,X1)
        | k4_relat_1(u1_orders_2(sK0)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_254])])).

fof(f2069,plain,
    ( u1_orders_2(k7_lattice3(sK0)) = k4_relat_1(u1_orders_2(sK0))
    | ~ spl9_232
    | ~ spl9_234
    | ~ spl9_254 ),
    inference(subsumption_resolution,[],[f2067,f1883])).

fof(f1883,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl9_234 ),
    inference(avatar_component_clause,[],[f1882])).

fof(f2067,plain,
    ( u1_orders_2(k7_lattice3(sK0)) = k4_relat_1(u1_orders_2(sK0))
    | ~ m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl9_232
    | ~ spl9_254 ),
    inference(trivial_inequality_removal,[],[f2065])).

fof(f2065,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | u1_orders_2(k7_lattice3(sK0)) = k4_relat_1(u1_orders_2(sK0))
    | ~ m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl9_232
    | ~ spl9_254 ),
    inference(superposition,[],[f2036,f1867])).

fof(f1867,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_232 ),
    inference(avatar_component_clause,[],[f1866])).

fof(f2036,plain,
    ( ! [X0,X1] :
        ( k7_lattice3(sK0) != g1_orders_2(X0,X1)
        | k4_relat_1(u1_orders_2(sK0)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
    | ~ spl9_254 ),
    inference(avatar_component_clause,[],[f2035])).

fof(f2061,plain,
    ( spl9_254
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f1473,f781,f2035])).

fof(f781,plain,
    ( spl9_110
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).

fof(f1473,plain,
    ( ! [X0,X1] :
        ( k7_lattice3(sK0) != g1_orders_2(X0,X1)
        | k4_relat_1(u1_orders_2(sK0)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
    | ~ spl9_110 ),
    inference(superposition,[],[f117,f782])).

fof(f782,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0)))
    | ~ spl9_110 ),
    inference(avatar_component_clause,[],[f781])).

fof(f117,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',free_g1_orders_2)).

fof(f1884,plain,
    ( spl9_234
    | ~ spl9_92
    | ~ spl9_140
    | ~ spl9_222 ),
    inference(avatar_split_clause,[],[f1849,f1773,f958,f690,f1882])).

fof(f690,plain,
    ( spl9_92
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f958,plain,
    ( spl9_140
  <=> m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).

fof(f1773,plain,
    ( spl9_222
  <=> ! [X5,X4] :
        ( k7_lattice3(sK0) != g1_orders_2(X4,X5)
        | u1_struct_0(sK0) = X4
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_222])])).

fof(f1849,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl9_92
    | ~ spl9_140
    | ~ spl9_222 ),
    inference(backward_demodulation,[],[f1846,f959])).

fof(f959,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)))))
    | ~ spl9_140 ),
    inference(avatar_component_clause,[],[f958])).

fof(f1846,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ spl9_92
    | ~ spl9_140
    | ~ spl9_222 ),
    inference(subsumption_resolution,[],[f1844,f959])).

fof(f1844,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)))))
    | ~ spl9_92
    | ~ spl9_222 ),
    inference(trivial_inequality_removal,[],[f1841])).

fof(f1841,plain,
    ( k7_lattice3(sK0) != k7_lattice3(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k7_lattice3(sK0))
    | ~ m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)))))
    | ~ spl9_92
    | ~ spl9_222 ),
    inference(superposition,[],[f1774,f691])).

fof(f691,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_92 ),
    inference(avatar_component_clause,[],[f690])).

fof(f1774,plain,
    ( ! [X4,X5] :
        ( k7_lattice3(sK0) != g1_orders_2(X4,X5)
        | u1_struct_0(sK0) = X4
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4))) )
    | ~ spl9_222 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f1868,plain,
    ( spl9_232
    | ~ spl9_92
    | ~ spl9_140
    | ~ spl9_222 ),
    inference(avatar_split_clause,[],[f1851,f1773,f958,f690,f1866])).

fof(f1851,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_92
    | ~ spl9_140
    | ~ spl9_222 ),
    inference(backward_demodulation,[],[f1846,f691])).

fof(f1775,plain,
    ( spl9_222
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f470,f463,f1773])).

fof(f463,plain,
    ( spl9_64
  <=> k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f470,plain,
    ( ! [X4,X5] :
        ( k7_lattice3(sK0) != g1_orders_2(X4,X5)
        | u1_struct_0(sK0) = X4
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X4))) )
    | ~ spl9_64 ),
    inference(superposition,[],[f116,f464])).

fof(f464,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f463])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f990,plain,
    ( ~ spl9_140
    | spl9_143 ),
    inference(avatar_contradiction_clause,[],[f989])).

fof(f989,plain,
    ( $false
    | ~ spl9_140
    | ~ spl9_143 ),
    inference(subsumption_resolution,[],[f982,f969])).

fof(f969,plain,
    ( ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_143 ),
    inference(avatar_component_clause,[],[f968])).

fof(f968,plain,
    ( spl9_143
  <=> ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_143])])).

fof(f982,plain,
    ( v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_140 ),
    inference(resolution,[],[f959,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',cc1_relset_1)).

fof(f976,plain,
    ( ~ spl9_143
    | spl9_144
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f839,f608,f974,f968])).

fof(f608,plain,
    ( spl9_84
  <=> r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f839,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k4_relat_1(u1_orders_2(k7_lattice3(sK0))))
    | ~ v1_relat_1(u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_84 ),
    inference(resolution,[],[f609,f296])).

fof(f296,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X4),X0)
      | r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f131,f94])).

fof(f131,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k4_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | k4_relat_1(X0) != X1
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f609,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f608])).

fof(f960,plain,
    ( spl9_140
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f527,f139,f958])).

fof(f527,plain,
    ( m1_subset_1(u1_orders_2(k7_lattice3(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(sK0)),u1_struct_0(k7_lattice3(sK0)))))
    | ~ spl9_0 ),
    inference(resolution,[],[f222,f140])).

fof(f222,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(k7_lattice3(X0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k7_lattice3(X0)),u1_struct_0(k7_lattice3(X0))))) ) ),
    inference(resolution,[],[f102,f105])).

fof(f105,plain,(
    ! [X0] :
      ( l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( l1_orders_2(k7_lattice3(X0))
        & v1_orders_2(k7_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',dt_k7_lattice3)).

fof(f102,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',dt_u1_orders_2)).

fof(f830,plain,
    ( spl9_120
    | ~ spl9_0
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f821,f238,f174,f167,f139,f828])).

fof(f238,plain,
    ( spl9_22
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f821,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl9_0
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f820,f140])).

fof(f820,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_8
    | ~ spl9_10
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f819,f168])).

fof(f819,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_10
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f818,f175])).

fof(f818,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_22 ),
    inference(resolution,[],[f239,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f239,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f238])).

fof(f823,plain,
    ( spl9_49
    | ~ spl9_50
    | ~ spl9_52
    | ~ spl9_82
    | spl9_87
    | ~ spl9_88 ),
    inference(avatar_contradiction_clause,[],[f822])).

fof(f822,plain,
    ( $false
    | ~ spl9_49
    | ~ spl9_50
    | ~ spl9_52
    | ~ spl9_82
    | ~ spl9_87
    | ~ spl9_88 ),
    inference(unit_resulting_resolution,[],[f600,f640,f392,f400,f650,f380,f321])).

fof(f321,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v1_xboole_0(u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(resolution,[],[f109,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',t2_subset)).

fof(f380,plain,
    ( ~ r1_orders_2(k7_lattice3(sK0),sK2,sK1)
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl9_49
  <=> ~ r1_orders_2(k7_lattice3(sK0),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f650,plain,
    ( m1_subset_1(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f649])).

fof(f649,plain,
    ( spl9_88
  <=> m1_subset_1(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f400,plain,
    ( m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ spl9_52 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl9_52
  <=> m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f392,plain,
    ( m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl9_50
  <=> m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f640,plain,
    ( ~ v1_xboole_0(u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_87 ),
    inference(avatar_component_clause,[],[f639])).

fof(f639,plain,
    ( spl9_87
  <=> ~ v1_xboole_0(u1_orders_2(k7_lattice3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f600,plain,
    ( l1_orders_2(k7_lattice3(sK0))
    | ~ spl9_82 ),
    inference(avatar_component_clause,[],[f599])).

fof(f599,plain,
    ( spl9_82
  <=> l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f783,plain,
    ( spl9_110
    | ~ spl9_28
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f769,f463,f271,f781])).

fof(f271,plain,
    ( spl9_28
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f769,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k4_relat_1(u1_orders_2(sK0)))
    | ~ spl9_28
    | ~ spl9_64 ),
    inference(backward_demodulation,[],[f283,f464])).

fof(f283,plain,
    ( k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)) = k4_relat_1(u1_orders_2(sK0))
    | ~ spl9_28 ),
    inference(resolution,[],[f272,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',redefinition_k3_relset_1)).

fof(f272,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f271])).

fof(f692,plain,
    ( spl9_92
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f445,f139,f690])).

fof(f445,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(k7_lattice3(sK0)),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_0 ),
    inference(resolution,[],[f225,f140])).

fof(f225,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0))) ) ),
    inference(subsumption_resolution,[],[f224,f105])).

fof(f224,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(k7_lattice3(X0)),u1_orders_2(k7_lattice3(X0)))
      | ~ l1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f106,f104])).

fof(f104,plain,(
    ! [X0] :
      ( v1_orders_2(k7_lattice3(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v1_orders_2(X0)
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',abstractness_v1_orders_2)).

fof(f651,plain,
    ( spl9_88
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f625,f608,f649])).

fof(f625,plain,
    ( m1_subset_1(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_84 ),
    inference(resolution,[],[f609,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',t1_subset)).

fof(f641,plain,
    ( ~ spl9_87
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f627,f608,f639])).

fof(f627,plain,
    ( ~ v1_xboole_0(u1_orders_2(k7_lattice3(sK0)))
    | ~ spl9_84 ),
    inference(resolution,[],[f609,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',t7_boole)).

fof(f615,plain,
    ( ~ spl9_0
    | spl9_83 ),
    inference(avatar_contradiction_clause,[],[f614])).

fof(f614,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_83 ),
    inference(subsumption_resolution,[],[f612,f140])).

fof(f612,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl9_83 ),
    inference(resolution,[],[f603,f105])).

fof(f603,plain,
    ( ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl9_83 ),
    inference(avatar_component_clause,[],[f602])).

fof(f602,plain,
    ( spl9_83
  <=> ~ l1_orders_2(k7_lattice3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f610,plain,
    ( ~ spl9_83
    | spl9_84
    | ~ spl9_48
    | ~ spl9_50
    | ~ spl9_52 ),
    inference(avatar_split_clause,[],[f590,f399,f391,f382,f608,f602])).

fof(f382,plain,
    ( spl9_48
  <=> r1_orders_2(k7_lattice3(sK0),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f590,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl9_48
    | ~ spl9_50
    | ~ spl9_52 ),
    inference(subsumption_resolution,[],[f589,f400])).

fof(f589,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl9_48
    | ~ spl9_50 ),
    inference(subsumption_resolution,[],[f385,f392])).

fof(f385,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(k7_lattice3(sK0))
    | ~ spl9_48 ),
    inference(resolution,[],[f383,f108])).

fof(f383,plain,
    ( r1_orders_2(k7_lattice3(sK0),sK2,sK1)
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f382])).

fof(f465,plain,
    ( spl9_64
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f259,f139,f463])).

fof(f259,plain,
    ( k7_lattice3(sK0) = g1_orders_2(u1_struct_0(sK0),k3_relset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_orders_2(sK0)))
    | ~ spl9_0 ),
    inference(resolution,[],[f103,f140])).

fof(f103,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k7_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k3_relset_1(u1_struct_0(X0),u1_struct_0(X0),u1_orders_2(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',d5_lattice3)).

fof(f401,plain,
    ( spl9_52
    | ~ spl9_0
    | ~ spl9_10
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f377,f364,f174,f139,f399])).

fof(f364,plain,
    ( spl9_46
  <=> k8_lattice3(sK0,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f377,plain,
    ( m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ spl9_0
    | ~ spl9_10
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f376,f140])).

fof(f376,plain,
    ( m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl9_10
    | ~ spl9_46 ),
    inference(subsumption_resolution,[],[f375,f175])).

fof(f375,plain,
    ( m1_subset_1(sK2,u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_46 ),
    inference(superposition,[],[f118,f365])).

fof(f365,plain,
    ( k8_lattice3(sK0,sK2) = sK2
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f364])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k8_lattice3(X0,X1),u1_struct_0(k7_lattice3(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',dt_k8_lattice3)).

fof(f393,plain,
    ( spl9_50
    | ~ spl9_0
    | ~ spl9_8
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f370,f350,f167,f139,f391])).

fof(f350,plain,
    ( spl9_42
  <=> k8_lattice3(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f370,plain,
    ( m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ spl9_0
    | ~ spl9_8
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f369,f140])).

fof(f369,plain,
    ( m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl9_8
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f368,f168])).

fof(f368,plain,
    ( m1_subset_1(sK1,u1_struct_0(k7_lattice3(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl9_42 ),
    inference(superposition,[],[f118,f351])).

fof(f351,plain,
    ( k8_lattice3(sK0,sK1) = sK1
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f350])).

fof(f384,plain,
    ( spl9_48
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(avatar_split_clause,[],[f374,f364,f357,f382])).

fof(f357,plain,
    ( spl9_44
  <=> r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f374,plain,
    ( r1_orders_2(k7_lattice3(sK0),sK2,sK1)
    | ~ spl9_44
    | ~ spl9_46 ),
    inference(backward_demodulation,[],[f365,f358])).

fof(f358,plain,
    ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),sK1)
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f357])).

fof(f366,plain,
    ( spl9_46
    | ~ spl9_10
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f343,f277,f174,f364])).

fof(f277,plain,
    ( spl9_30
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k8_lattice3(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f343,plain,
    ( k8_lattice3(sK0,sK2) = sK2
    | ~ spl9_10
    | ~ spl9_30 ),
    inference(resolution,[],[f278,f175])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k8_lattice3(sK0,X0) = X0 )
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f277])).

fof(f359,plain,
    ( spl9_44
    | ~ spl9_8
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f345,f277,f244,f167,f357])).

fof(f244,plain,
    ( spl9_24
  <=> r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f345,plain,
    ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),sK1)
    | ~ spl9_8
    | ~ spl9_24
    | ~ spl9_30 ),
    inference(backward_demodulation,[],[f342,f245])).

fof(f245,plain,
    ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f244])).

fof(f342,plain,
    ( k8_lattice3(sK0,sK1) = sK1
    | ~ spl9_8
    | ~ spl9_30 ),
    inference(resolution,[],[f278,f168])).

fof(f352,plain,
    ( spl9_42
    | ~ spl9_8
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f342,f277,f167,f350])).

fof(f328,plain,
    ( spl9_38
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f297,f293,f326])).

fof(f326,plain,
    ( spl9_38
  <=> u1_orders_2(sK0) = k4_relat_1(k4_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f293,plain,
    ( spl9_32
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f297,plain,
    ( u1_orders_2(sK0) = k4_relat_1(k4_relat_1(u1_orders_2(sK0)))
    | ~ spl9_32 ),
    inference(resolution,[],[f294,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',involutiveness_k4_relat_1)).

fof(f294,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f293])).

fof(f295,plain,
    ( spl9_32
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f284,f271,f293])).

fof(f284,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl9_28 ),
    inference(resolution,[],[f272,f123])).

fof(f279,plain,
    ( spl9_30
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f230,f139,f277])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k8_lattice3(sK0,X0) = X0 )
    | ~ spl9_0 ),
    inference(resolution,[],[f107,f140])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k8_lattice3(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k8_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k8_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',d6_lattice3)).

fof(f273,plain,
    ( spl9_28
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f220,f139,f271])).

fof(f220,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl9_0 ),
    inference(resolution,[],[f102,f140])).

fof(f253,plain,
    ( ~ spl9_23
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f252,f244,f235])).

fof(f252,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f92,f245])).

fof(f92,plain,
    ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,
    ( ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
      | ~ r1_orders_2(sK0,sK1,sK2) )
    & ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
      | r1_orders_2(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f71,f74,f73,f72])).

fof(f72,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                  | r1_orders_2(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,X2),k8_lattice3(sK0,X1))
                | ~ r1_orders_2(sK0,X1,X2) )
              & ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,X2),k8_lattice3(sK0,X1))
                | r1_orders_2(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | ~ r1_orders_2(X0,X1,X2) )
              & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,sK1))
              | ~ r1_orders_2(X0,sK1,X2) )
            & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,sK1))
              | r1_orders_2(X0,sK1,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
            | ~ r1_orders_2(X0,X1,X2) )
          & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
            | r1_orders_2(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,sK2),k8_lattice3(X0,X1))
          | ~ r1_orders_2(X0,X1,sK2) )
        & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,sK2),k8_lattice3(X0,X1))
          | r1_orders_2(X0,X1,sK2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | ~ r1_orders_2(X0,X1,X2) )
              & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | ~ r1_orders_2(X0,X1,X2) )
              & ( r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1))
                | r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <~> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r1_orders_2(X0,X1,X2)
                <=> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r1_orders_2(k7_lattice3(X0),k8_lattice3(X0,X2),k8_lattice3(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t9_lattice3.p',t9_lattice3)).

fof(f246,plain,
    ( spl9_22
    | spl9_24 ),
    inference(avatar_split_clause,[],[f91,f244,f238])).

fof(f91,plain,
    ( r1_orders_2(k7_lattice3(sK0),k8_lattice3(sK0,sK2),k8_lattice3(sK0,sK1))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f75])).

fof(f176,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f90,f174])).

fof(f90,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f75])).

fof(f169,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f89,f167])).

fof(f89,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f75])).

fof(f141,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f88,f139])).

fof(f88,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f75])).
%------------------------------------------------------------------------------
