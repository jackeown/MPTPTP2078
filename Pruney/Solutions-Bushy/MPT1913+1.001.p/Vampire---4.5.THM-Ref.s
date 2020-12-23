%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1913+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 249 expanded)
%              Number of leaves         :   27 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  541 (1517 expanded)
%              Number of equality atoms :   90 ( 222 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f80,f90,f96,f102,f107,f125,f135,f140,f146,f151,f154])).

fof(f154,plain,
    ( spl5_8
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_4
    | ~ spl5_3
    | ~ spl5_2
    | spl5_20 ),
    inference(avatar_split_clause,[],[f153,f149,f54,f58,f62,f66,f70,f74,f78])).

fof(f78,plain,
    ( spl5_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f74,plain,
    ( spl5_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f70,plain,
    ( spl5_6
  <=> v4_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f66,plain,
    ( spl5_5
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f62,plain,
    ( spl5_4
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f58,plain,
    ( spl5_3
  <=> v2_pralg_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f54,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f149,plain,
    ( spl5_20
  <=> u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) = u1_struct_0(k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f153,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ v2_pralg_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0)
    | spl5_20 ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( u1_struct_0(k1_funct_1(sK1,sK2)) != u1_struct_0(k1_funct_1(sK1,sK2))
    | ~ m1_subset_1(sK2,sK0)
    | ~ v2_pralg_1(sK1)
    | ~ v1_partfun1(sK1,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v4_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | v1_xboole_0(sK0)
    | spl5_20 ),
    inference(superposition,[],[f150,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1)
        & ~ v1_xboole_0(X0) )
     => k10_pralg_1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k10_pralg_1)).

fof(f150,plain,
    ( u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) != u1_struct_0(k1_funct_1(sK1,sK2))
    | spl5_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( ~ spl5_20
    | spl5_1
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f147,f144,f50,f149])).

fof(f50,plain,
    ( spl5_1
  <=> k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f144,plain,
    ( spl5_19
  <=> k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f147,plain,
    ( u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) != u1_struct_0(k1_funct_1(sK1,sK2))
    | spl5_1
    | ~ spl5_19 ),
    inference(superposition,[],[f51,f145])).

fof(f145,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k1_funct_1(sK1,sK2))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f144])).

fof(f51,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f146,plain,
    ( spl5_19
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f142,f138,f105,f54,f144])).

fof(f105,plain,
    ( spl5_12
  <=> k1_funct_1(sK1,sK2) = sK4(sK1,k12_pralg_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f138,plain,
    ( spl5_18
  <=> ! [X0] :
        ( k1_funct_1(k12_pralg_1(sK0,sK1),X0) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X0))
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f142,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(k1_funct_1(sK1,sK2))
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f141,f106])).

fof(f106,plain,
    ( k1_funct_1(sK1,sK2) = sK4(sK1,k12_pralg_1(sK0,sK1),sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f105])).

fof(f141,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),sK2))
    | ~ spl5_2
    | ~ spl5_18 ),
    inference(resolution,[],[f139,f55])).

fof(f55,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X0) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X0)) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl5_8
    | spl5_18
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f136,f133,f138,f78])).

fof(f133,plain,
    ( spl5_17
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X0) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f136,plain,
    ( ! [X0] :
        ( k1_funct_1(k12_pralg_1(sK0,sK1),X0) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X0))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl5_17 ),
    inference(resolution,[],[f134,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X0) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X0)) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl5_17
    | ~ spl5_6
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f131,f123,f62,f70,f133])).

fof(f123,plain,
    ( spl5_15
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v4_relat_1(sK1,X1)
        | ~ v1_partfun1(sK1,X1)
        | k1_funct_1(k12_pralg_1(X1,sK1),X0) = u1_struct_0(sK4(sK1,k12_pralg_1(X1,sK1),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK1,sK0)
        | ~ r2_hidden(X0,sK0)
        | k1_funct_1(k12_pralg_1(sK0,sK1),X0) = u1_struct_0(sK4(sK1,k12_pralg_1(sK0,sK1),X0)) )
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(resolution,[],[f124,f63])).

fof(f63,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK1,X1)
        | ~ v4_relat_1(sK1,X1)
        | ~ r2_hidden(X0,X1)
        | k1_funct_1(k12_pralg_1(X1,sK1),X0) = u1_struct_0(sK4(sK1,k12_pralg_1(X1,sK1),X0)) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f125,plain,
    ( ~ spl5_7
    | ~ spl5_5
    | spl5_15
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f121,f58,f123,f66,f74])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_funct_1(k12_pralg_1(X1,sK1),X0) = u1_struct_0(sK4(sK1,k12_pralg_1(X1,sK1),X0))
        | ~ v1_partfun1(sK1,X1)
        | ~ v1_funct_1(sK1)
        | ~ v4_relat_1(sK1,X1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f81,f59])).

fof(f59,plain,
    ( v2_pralg_1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f81,plain,(
    ! [X0,X5,X1] :
      ( ~ v2_pralg_1(X1)
      | ~ r2_hidden(X5,X0)
      | k1_funct_1(k12_pralg_1(X0,X1),X5) = u1_struct_0(sK4(X1,k12_pralg_1(X0,X1),X5))
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f38,f37,f36,f35,f46])).

fof(f46,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(k12_pralg_1(X0,X1),X5) = u1_struct_0(sK4(X1,k12_pralg_1(X0,X1),X5))
      | ~ r2_hidden(X5,X0)
      | ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5))
      | ~ r2_hidden(X5,X0)
      | k12_pralg_1(X0,X1) != X2
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k12_pralg_1(X0,X1) = X2
              | ( ! [X4] :
                    ( u1_struct_0(X4) != k1_funct_1(X2,sK3(X0,X1,X2))
                    | k1_funct_1(X1,sK3(X0,X1,X2)) != X4
                    | ~ l1_struct_0(X4) )
                & r2_hidden(sK3(X0,X1,X2),X0) ) )
            & ( ! [X5] :
                  ( ( k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5))
                    & k1_funct_1(X1,X5) = sK4(X1,X2,X5)
                    & l1_struct_0(sK4(X1,X2,X5)) )
                  | ~ r2_hidden(X5,X0) )
              | k12_pralg_1(X0,X1) != X2 ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f22,f24,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X3) != u1_struct_0(X4)
              | k1_funct_1(X1,X3) != X4
              | ~ l1_struct_0(X4) )
          & r2_hidden(X3,X0) )
     => ( ! [X4] :
            ( u1_struct_0(X4) != k1_funct_1(X2,sK3(X0,X1,X2))
            | k1_funct_1(X1,sK3(X0,X1,X2)) != X4
            | ~ l1_struct_0(X4) )
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X5,X2,X1] :
      ( ? [X6] :
          ( k1_funct_1(X2,X5) = u1_struct_0(X6)
          & k1_funct_1(X1,X5) = X6
          & l1_struct_0(X6) )
     => ( k1_funct_1(X2,X5) = u1_struct_0(sK4(X1,X2,X5))
        & k1_funct_1(X1,X5) = sK4(X1,X2,X5)
        & l1_struct_0(sK4(X1,X2,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k12_pralg_1(X0,X1) = X2
              | ? [X3] :
                  ( ! [X4] :
                      ( k1_funct_1(X2,X3) != u1_struct_0(X4)
                      | k1_funct_1(X1,X3) != X4
                      | ~ l1_struct_0(X4) )
                  & r2_hidden(X3,X0) ) )
            & ( ! [X5] :
                  ( ? [X6] :
                      ( k1_funct_1(X2,X5) = u1_struct_0(X6)
                      & k1_funct_1(X1,X5) = X6
                      & l1_struct_0(X6) )
                  | ~ r2_hidden(X5,X0) )
              | k12_pralg_1(X0,X1) != X2 ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k12_pralg_1(X0,X1) = X2
              | ? [X3] :
                  ( ! [X4] :
                      ( k1_funct_1(X2,X3) != u1_struct_0(X4)
                      | k1_funct_1(X1,X3) != X4
                      | ~ l1_struct_0(X4) )
                  & r2_hidden(X3,X0) ) )
            & ( ! [X3] :
                  ( ? [X4] :
                      ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                      & k1_funct_1(X1,X3) = X4
                      & l1_struct_0(X4) )
                  | ~ r2_hidden(X3,X0) )
              | k12_pralg_1(X0,X1) != X2 ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ( ? [X4] :
                    ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                    & k1_funct_1(X1,X3) = X4
                    & l1_struct_0(X4) )
                | ~ r2_hidden(X3,X0) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ( ? [X4] :
                    ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                    & k1_funct_1(X1,X3) = X4
                    & l1_struct_0(X4) )
                | ~ r2_hidden(X3,X0) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( k12_pralg_1(X0,X1) = X2
          <=> ! [X3] :
                ~ ( ! [X4] :
                      ( l1_struct_0(X4)
                     => ~ ( k1_funct_1(X2,X3) = u1_struct_0(X4)
                          & k1_funct_1(X1,X3) = X4 ) )
                  & r2_hidden(X3,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pralg_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) )
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v2_pralg_1(X1)
        & v1_partfun1(X1,X0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(k12_pralg_1(X0,X1),X0)
        & v1_funct_1(k12_pralg_1(X0,X1))
        & v4_relat_1(k12_pralg_1(X0,X1),X0)
        & v1_relat_1(k12_pralg_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_pralg_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f107,plain,
    ( spl5_12
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f103,f100,f54,f105])).

fof(f100,plain,
    ( spl5_11
  <=> ! [X0] :
        ( k1_funct_1(sK1,X0) = sK4(sK1,k12_pralg_1(sK0,sK1),X0)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f103,plain,
    ( k1_funct_1(sK1,sK2) = sK4(sK1,k12_pralg_1(sK0,sK1),sK2)
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(resolution,[],[f101,f55])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k1_funct_1(sK1,X0) = sK4(sK1,k12_pralg_1(sK0,sK1),X0) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl5_8
    | spl5_11
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f97,f93,f100,f78])).

fof(f93,plain,
    ( spl5_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = sK4(sK1,k12_pralg_1(sK0,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f97,plain,
    ( ! [X0] :
        ( k1_funct_1(sK1,X0) = sK4(sK1,k12_pralg_1(sK0,sK1),X0)
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl5_10 ),
    inference(resolution,[],[f94,f34])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = sK4(sK1,k12_pralg_1(sK0,sK1),X0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f96,plain,
    ( spl5_10
    | ~ spl5_6
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f91,f88,f62,f70,f93])).

fof(f88,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ v4_relat_1(sK1,X1)
        | ~ v1_partfun1(sK1,X1)
        | k1_funct_1(sK1,X0) = sK4(sK1,k12_pralg_1(X1,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

% (30306)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% (30294)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f91,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK1,sK0)
        | ~ r2_hidden(X0,sK0)
        | k1_funct_1(sK1,X0) = sK4(sK1,k12_pralg_1(sK0,sK1),X0) )
    | ~ spl5_4
    | ~ spl5_9 ),
    inference(resolution,[],[f89,f63])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(sK1,X1)
        | ~ v4_relat_1(sK1,X1)
        | ~ r2_hidden(X0,X1)
        | k1_funct_1(sK1,X0) = sK4(sK1,k12_pralg_1(X1,sK1),X0) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,
    ( ~ spl5_7
    | ~ spl5_5
    | spl5_9
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f84,f58,f88,f66,f74])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_funct_1(sK1,X0) = sK4(sK1,k12_pralg_1(X1,sK1),X0)
        | ~ v1_partfun1(sK1,X1)
        | ~ v1_funct_1(sK1)
        | ~ v4_relat_1(sK1,X1)
        | ~ v1_relat_1(sK1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f82,f59])).

fof(f82,plain,(
    ! [X0,X5,X1] :
      ( ~ v2_pralg_1(X1)
      | ~ r2_hidden(X5,X0)
      | k1_funct_1(X1,X5) = sK4(X1,k12_pralg_1(X0,X1),X5)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f38,f37,f36,f35,f47])).

fof(f47,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,X5) = sK4(X1,k12_pralg_1(X0,X1),X5)
      | ~ r2_hidden(X5,X0)
      | ~ v1_partfun1(k12_pralg_1(X0,X1),X0)
      | ~ v1_funct_1(k12_pralg_1(X0,X1))
      | ~ v4_relat_1(k12_pralg_1(X0,X1),X0)
      | ~ v1_relat_1(k12_pralg_1(X0,X1))
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X1,X5) = sK4(X1,X2,X5)
      | ~ r2_hidden(X5,X0)
      | k12_pralg_1(X0,X1) != X2
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v2_pralg_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f26,f78])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2))
    & m1_subset_1(sK2,sK0)
    & v2_pralg_1(sK1)
    & v1_partfun1(sK1,sK0)
    & v1_funct_1(sK1)
    & v4_relat_1(sK1,sK0)
    & v1_relat_1(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
                & m1_subset_1(X2,X0) )
            & v2_pralg_1(X1)
            & v1_partfun1(X1,X0)
            & v1_funct_1(X1)
            & v4_relat_1(X1,X0)
            & v1_relat_1(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(sK0,X1),X2) != u1_struct_0(k10_pralg_1(sK0,X1,X2))
              & m1_subset_1(X2,sK0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,sK0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,sK0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_funct_1(k12_pralg_1(sK0,X1),X2) != u1_struct_0(k10_pralg_1(sK0,X1,X2))
            & m1_subset_1(X2,sK0) )
        & v2_pralg_1(X1)
        & v1_partfun1(X1,sK0)
        & v1_funct_1(X1)
        & v4_relat_1(X1,sK0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( k1_funct_1(k12_pralg_1(sK0,sK1),X2) != u1_struct_0(k10_pralg_1(sK0,sK1,X2))
          & m1_subset_1(X2,sK0) )
      & v2_pralg_1(sK1)
      & v1_partfun1(sK1,sK0)
      & v1_funct_1(sK1)
      & v4_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( k1_funct_1(k12_pralg_1(sK0,sK1),X2) != u1_struct_0(k10_pralg_1(sK0,sK1,X2))
        & m1_subset_1(X2,sK0) )
   => ( k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2))
      & m1_subset_1(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_funct_1(k12_pralg_1(X0,X1),X2) != u1_struct_0(k10_pralg_1(X0,X1,X2))
              & m1_subset_1(X2,X0) )
          & v2_pralg_1(X1)
          & v1_partfun1(X1,X0)
          & v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v1_relat_1(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v2_pralg_1(X1)
              & v1_partfun1(X1,X0)
              & v1_funct_1(X1)
              & v4_relat_1(X1,X0)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v2_pralg_1(X1)
            & v1_partfun1(X1,X0)
            & v1_funct_1(X1)
            & v4_relat_1(X1,X0)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => k1_funct_1(k12_pralg_1(X0,X1),X2) = u1_struct_0(k10_pralg_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_6)).

fof(f76,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f27,f74])).

fof(f27,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f72,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v1_partfun1(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    v2_pralg_1(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f33,f50])).

fof(f33,plain,(
    k1_funct_1(k12_pralg_1(sK0,sK1),sK2) != u1_struct_0(k10_pralg_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
