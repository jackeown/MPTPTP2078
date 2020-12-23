%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1749+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  235 ( 760 expanded)
%              Number of leaves         :   52 ( 354 expanded)
%              Depth                    :   22
%              Number of atoms          : 1300 (5812 expanded)
%              Number of equality atoms :  117 ( 479 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f343,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f90,f95,f100,f105,f110,f115,f122,f127,f132,f137,f143,f151,f157,f162,f167,f172,f177,f182,f188,f197,f202,f214,f219,f260,f267,f289,f296,f310,f326,f332,f336,f338,f342])).

fof(f342,plain,
    ( ~ spl6_8
    | ~ spl6_19
    | spl6_35
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f341])).

fof(f341,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_19
    | spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f340,f104])).

fof(f104,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f340,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl6_19
    | spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f339,f166])).

fof(f166,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_19
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f339,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f330,f308])).

fof(f308,plain,
    ( sK4 != k7_relat_1(sK3,u1_struct_0(sK2))
    | spl6_35 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl6_35
  <=> sK4 = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f330,plain,
    ( sK4 = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | ~ spl6_36 ),
    inference(superposition,[],[f63,f325])).

fof(f325,plain,
    ( sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl6_36
  <=> sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f338,plain,
    ( ~ spl6_8
    | ~ spl6_19
    | spl6_35
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_19
    | spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f329,f308])).

fof(f329,plain,
    ( sK4 = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl6_8
    | ~ spl6_19
    | ~ spl6_36 ),
    inference(superposition,[],[f189,f325])).

fof(f189,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl6_8
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f104,f166,f63])).

fof(f336,plain,
    ( ~ spl6_8
    | ~ spl6_19
    | spl6_35
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_19
    | spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f334,f104])).

fof(f334,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl6_19
    | spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f333,f166])).

fof(f333,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f328,f308])).

fof(f328,plain,
    ( sK4 = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK3)
    | ~ spl6_36 ),
    inference(superposition,[],[f325,f63])).

fof(f332,plain,
    ( ~ spl6_8
    | ~ spl6_19
    | spl6_35
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl6_8
    | ~ spl6_19
    | spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f327,f308])).

fof(f327,plain,
    ( sK4 = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ spl6_8
    | ~ spl6_19
    | ~ spl6_36 ),
    inference(superposition,[],[f325,f189])).

fof(f326,plain,
    ( spl6_36
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | spl6_17
    | spl6_18
    | ~ spl6_19
    | spl6_20
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f313,f303,f185,f174,f169,f164,f159,f154,f134,f129,f107,f102,f323])).

fof(f107,plain,
    ( spl6_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f129,plain,
    ( spl6_13
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f134,plain,
    ( spl6_14
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f154,plain,
    ( spl6_17
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f159,plain,
    ( spl6_18
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f169,plain,
    ( spl6_20
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f174,plain,
    ( spl6_21
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f185,plain,
    ( spl6_23
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f303,plain,
    ( spl6_34
  <=> k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f313,plain,
    ( sK4 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | spl6_17
    | spl6_18
    | ~ spl6_19
    | spl6_20
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f104,f109,f161,f156,f171,f131,f136,f187,f166,f176,f305,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
                        & r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
                        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f35])).

fof(f35,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
          & r2_hidden(X5,X3)
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X2,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X4,sK5(X0,X1,X2,X3,X4))
        & r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(X0,X1,X2,X3) = X4
                      | ? [X5] :
                          ( k3_funct_2(X0,X1,X2,X5) != k1_funct_1(X4,X5)
                          & r2_hidden(X5,X3)
                          & m1_subset_1(X5,X0) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                      | ~ v1_funct_2(X4,X3,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X4,X3,X1)
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => ( r2_hidden(X5,X3)
                             => k3_funct_2(X0,X1,X2,X5) = k1_funct_1(X4,X5) ) )
                       => k2_partfun1(X0,X1,X2,X3) = X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_funct_2)).

fof(f305,plain,
    ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f303])).

fof(f176,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f174])).

fof(f187,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f185])).

fof(f136,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f131,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f171,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f169])).

fof(f156,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f161,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f109,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f310,plain,
    ( spl6_34
    | spl6_35
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | spl6_17
    | spl6_18
    | ~ spl6_19
    | spl6_20
    | ~ spl6_21
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f301,f185,f174,f169,f164,f159,f154,f134,f129,f107,f102,f307,f303])).

fof(f301,plain,
    ( sK4 = k7_relat_1(sK3,u1_struct_0(sK2))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | spl6_17
    | spl6_18
    | ~ spl6_19
    | spl6_20
    | ~ spl6_21
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f300,f176])).

fof(f300,plain,
    ( sK4 = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | spl6_17
    | spl6_18
    | ~ spl6_19
    | spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f299,f109])).

fof(f299,plain,
    ( sK4 = k7_relat_1(sK3,u1_struct_0(sK2))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),sK4))
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_14
    | spl6_17
    | spl6_18
    | ~ spl6_19
    | spl6_20
    | ~ spl6_23 ),
    inference(resolution,[],[f272,f136])).

fof(f272,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
        | k7_relat_1(sK3,u1_struct_0(sK2)) = X0
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),X0)) )
    | ~ spl6_8
    | ~ spl6_13
    | spl6_17
    | spl6_18
    | ~ spl6_19
    | spl6_20
    | ~ spl6_23 ),
    inference(forward_demodulation,[],[f271,f189])).

fof(f271,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),X0))
        | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = X0 )
    | ~ spl6_8
    | ~ spl6_13
    | spl6_17
    | spl6_18
    | ~ spl6_19
    | spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f270,f156])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | v1_xboole_0(u1_struct_0(sK0))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),X0))
        | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = X0 )
    | ~ spl6_8
    | ~ spl6_13
    | spl6_18
    | ~ spl6_19
    | spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f269,f104])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(u1_struct_0(sK0))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),X0))
        | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = X0 )
    | ~ spl6_13
    | spl6_18
    | ~ spl6_19
    | spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f268,f166])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,u1_struct_0(sK2),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(u1_struct_0(sK0))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2),X0))
        | k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2)) = X0 )
    | ~ spl6_13
    | spl6_18
    | spl6_20
    | ~ spl6_23 ),
    inference(resolution,[],[f251,f131])).

fof(f251,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,u1_struct_0(sK1),X1)
        | ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
        | ~ v1_funct_1(X2)
        | v1_xboole_0(X1)
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0))
        | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0 )
    | spl6_18
    | spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f250,f171])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
        | ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),X1)
        | ~ v1_funct_1(X2)
        | v1_xboole_0(X1)
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0))
        | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0
        | v1_xboole_0(u1_struct_0(sK2)) )
    | spl6_18
    | spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f249,f161])).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
        | ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),X1)
        | ~ v1_funct_1(X2)
        | v1_xboole_0(X1)
        | v1_xboole_0(u1_struct_0(sK1))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0))
        | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0
        | v1_xboole_0(u1_struct_0(sK2)) )
    | spl6_20
    | ~ spl6_23 ),
    inference(subsumption_resolution,[],[f248,f187])).

fof(f248,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
        | ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),X1)
        | ~ v1_funct_1(X2)
        | v1_xboole_0(X1)
        | v1_xboole_0(u1_struct_0(sK1))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0))
        | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0
        | v1_xboole_0(u1_struct_0(sK2)) )
    | spl6_20 ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
        | ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),X1)
        | ~ v1_funct_1(X2)
        | v1_xboole_0(X1)
        | v1_xboole_0(u1_struct_0(sK1))
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0)) = k1_funct_1(sK4,sK5(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2),X0))
        | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0
        | k2_partfun1(u1_struct_0(sK1),X1,X2,u1_struct_0(sK2)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
        | ~ v1_funct_2(X0,u1_struct_0(sK2),X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),X1)))
        | ~ v1_funct_2(X2,u1_struct_0(sK1),X1)
        | ~ v1_funct_1(X2)
        | v1_xboole_0(X1)
        | v1_xboole_0(u1_struct_0(sK1)) )
    | spl6_20 ),
    inference(resolution,[],[f231,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f231,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5(X0,X1,X2,u1_struct_0(sK2),X3),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
        | ~ v1_funct_2(X3,u1_struct_0(sK2),X1)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | v1_xboole_0(X1)
        | v1_xboole_0(X0)
        | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(X0,X1,X2,u1_struct_0(sK2),X3)) = k1_funct_1(sK4,sK5(X0,X1,X2,u1_struct_0(sK2),X3))
        | k2_partfun1(X0,X1,X2,u1_struct_0(sK2)) = X3 )
    | spl6_20 ),
    inference(subsumption_resolution,[],[f230,f171])).

fof(f230,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,u1_struct_0(sK2)) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),X1)))
      | ~ v1_funct_2(X3,u1_struct_0(sK2),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
      | v1_xboole_0(u1_struct_0(sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK5(X0,X1,X2,u1_struct_0(sK2),X3)) = k1_funct_1(sK4,sK5(X0,X1,X2,u1_struct_0(sK2),X3))
      | ~ m1_subset_1(sK5(X0,X1,X2,u1_struct_0(sK2),X3),u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f54,f51])).

fof(f51,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    & ! [X5] :
        ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
        | ~ r2_hidden(X5,u1_struct_0(sK2))
        | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f33,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                        & ! [X5] :
                            ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                            | ~ r2_hidden(X5,u1_struct_0(X2))
                            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                & m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(X1,sK0,X3,X2),X4)
                    & ! [X5] :
                        ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(sK0),X3,X5)
                        | ~ r2_hidden(X5,u1_struct_0(X2))
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(sK0))
                & v1_funct_1(X3) )
            & m1_pre_topc(X2,X1)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4)
                  & ! [X5] :
                      ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                      | ~ r2_hidden(X5,u1_struct_0(X2))
                      | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
              & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
              & v1_funct_1(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

% (19938)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,X2),X4)
                & ! [X5] :
                    ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                    | ~ r2_hidden(X5,u1_struct_0(X2))
                    | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
            & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
            & v1_funct_1(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4)
              & ! [X5] :
                  ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                  | ~ r2_hidden(X5,u1_struct_0(sK2))
                  | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X3) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,X3,sK2),X4)
            & ! [X5] :
                ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),X3,X5)
                | ~ r2_hidden(X5,u1_struct_0(sK2))
                | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X3,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4)
          & ! [X5] :
              ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5)
              | ~ r2_hidden(X5,u1_struct_0(sK2))
              | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X4] :
        ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),X4)
        & ! [X5] :
            ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5)
            | ~ r2_hidden(X5,u1_struct_0(sK2))
            | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK2),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
      & ! [X5] :
          ( k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,X5) = k1_funct_1(sK4,X5)
          | ~ r2_hidden(X5,u1_struct_0(sK2))
          | ~ m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4)
                      & ! [X5] :
                          ( k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5)
                          | ~ r2_hidden(X5,u1_struct_0(X2))
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X3) )
              & m1_pre_topc(X2,X1)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X1)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                         => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k1_funct_1(X4,X5) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),X3,X5) ) )
                       => r2_funct_2(u1_struct_0(X2),u1_struct_0(X0),k2_tmap_1(X1,X0,X3,X2),X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_tmap_1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X2,X3,X4),X3)
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f296,plain,
    ( ~ spl6_33
    | ~ spl6_15
    | spl6_31 ),
    inference(avatar_split_clause,[],[f290,f282,f140,f293])).

fof(f293,plain,
    ( spl6_33
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f140,plain,
    ( spl6_15
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f282,plain,
    ( spl6_31
  <=> m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f290,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ spl6_15
    | spl6_31 ),
    inference(unit_resulting_resolution,[],[f142,f284,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f284,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl6_31 ),
    inference(avatar_component_clause,[],[f282])).

fof(f142,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f289,plain,
    ( ~ spl6_31
    | spl6_32
    | ~ spl6_9
    | ~ spl6_14
    | spl6_17
    | spl6_20
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f280,f174,f169,f154,f134,f107,f286,f282])).

% (19953)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
fof(f286,plain,
    ( spl6_32
  <=> sK4 = k7_relat_1(sK4,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f280,plain,
    ( sK4 = k7_relat_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_9
    | ~ spl6_14
    | spl6_17
    | spl6_20
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f279,f190])).

fof(f190,plain,
    ( ! [X0] : k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f109,f176,f63])).

fof(f279,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK4 = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ spl6_9
    | ~ spl6_14
    | spl6_17
    | spl6_20
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f278,f171])).

fof(f278,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK4 = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl6_9
    | ~ spl6_14
    | spl6_17
    | spl6_20
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f277,f136])).

fof(f277,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK4 = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK0),sK4,u1_struct_0(sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl6_9
    | ~ spl6_14
    | spl6_17
    | spl6_20
    | ~ spl6_21 ),
    inference(resolution,[],[f276,f176])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
        | sK4 = k2_partfun1(X0,u1_struct_0(sK0),sK4,u1_struct_0(sK2))
        | ~ v1_funct_2(sK4,X0,u1_struct_0(sK0))
        | v1_xboole_0(X0) )
    | ~ spl6_9
    | ~ spl6_14
    | spl6_17
    | spl6_20
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f275,f156])).

fof(f275,plain,
    ( ! [X0] :
        ( sK4 = k2_partfun1(X0,u1_struct_0(sK0),sK4,u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))
        | ~ v1_funct_2(sK4,X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(X0) )
    | ~ spl6_9
    | ~ spl6_14
    | spl6_20
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f274,f171])).

fof(f274,plain,
    ( ! [X0] :
        ( sK4 = k2_partfun1(X0,u1_struct_0(sK0),sK4,u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))
        | ~ v1_funct_2(sK4,X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(X0) )
    | ~ spl6_9
    | ~ spl6_14
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f273,f136])).

fof(f273,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0))
        | sK4 = k2_partfun1(X0,u1_struct_0(sK0),sK4,u1_struct_0(sK2))
        | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0))
        | v1_xboole_0(u1_struct_0(sK2))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))
        | ~ v1_funct_2(sK4,X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(X0) )
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(resolution,[],[f238,f176])).

fof(f238,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_2(sK4,X3,X4)
        | sK4 = k2_partfun1(X5,X4,sK4,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X5))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
        | ~ v1_funct_2(sK4,X5,X4)
        | v1_xboole_0(X4)
        | v1_xboole_0(X5) )
    | ~ spl6_9 ),
    inference(resolution,[],[f236,f109])).

fof(f236,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X2,X3,X1)
      | k2_partfun1(X0,X1,X2,X3) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X2,X3,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f234])).

fof(f234,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X4,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X2,sK5(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f233,f53])).

fof(f233,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X4,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X2,sK5(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) ) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_funct_1(X4,sK5(X0,X1,X2,X3,X4)) != k1_funct_1(X2,sK5(X0,X1,X2,X3,X4))
      | k2_partfun1(X0,X1,X2,X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X4,X3,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f55,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f267,plain,
    ( ~ spl6_30
    | ~ spl6_6
    | spl6_28 ),
    inference(avatar_split_clause,[],[f261,f253,f92,f264])).

fof(f264,plain,
    ( spl6_30
  <=> m1_pre_topc(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f92,plain,
    ( spl6_6
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f253,plain,
    ( spl6_28
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f261,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ spl6_6
    | spl6_28 ),
    inference(unit_resulting_resolution,[],[f94,f255,f58])).

fof(f255,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f253])).

fof(f94,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f260,plain,
    ( ~ spl6_28
    | spl6_29
    | ~ spl6_8
    | ~ spl6_13
    | spl6_17
    | spl6_18
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f246,f164,f159,f154,f129,f102,f257,f253])).

fof(f257,plain,
    ( spl6_29
  <=> sK3 = k7_relat_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f246,plain,
    ( sK3 = k7_relat_1(sK3,u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_8
    | ~ spl6_13
    | spl6_17
    | spl6_18
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f245,f189])).

fof(f245,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | ~ spl6_8
    | ~ spl6_13
    | spl6_17
    | spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f244,f161])).

fof(f244,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_8
    | ~ spl6_13
    | spl6_17
    | spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f243,f131])).

fof(f243,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3 = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl6_8
    | ~ spl6_13
    | spl6_17
    | spl6_18
    | ~ spl6_19 ),
    inference(resolution,[],[f242,f166])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
        | sK3 = k2_partfun1(X0,u1_struct_0(sK0),sK3,u1_struct_0(sK1))
        | ~ v1_funct_2(sK3,X0,u1_struct_0(sK0))
        | v1_xboole_0(X0) )
    | ~ spl6_8
    | ~ spl6_13
    | spl6_17
    | spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f241,f156])).

fof(f241,plain,
    ( ! [X0] :
        ( sK3 = k2_partfun1(X0,u1_struct_0(sK0),sK3,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))
        | ~ v1_funct_2(sK3,X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(X0) )
    | ~ spl6_8
    | ~ spl6_13
    | spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f240,f161])).

fof(f240,plain,
    ( ! [X0] :
        ( sK3 = k2_partfun1(X0,u1_struct_0(sK0),sK3,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))
        | ~ v1_funct_2(sK3,X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(X0) )
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f239,f131])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0))
        | sK3 = k2_partfun1(X0,u1_struct_0(sK0),sK3,u1_struct_0(sK1))
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(X0))
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,u1_struct_0(sK0))))
        | ~ v1_funct_2(sK3,X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | v1_xboole_0(X0) )
    | ~ spl6_8
    | ~ spl6_19 ),
    inference(resolution,[],[f237,f166])).

fof(f237,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK3,X0,X1)
        | sK3 = k2_partfun1(X2,X1,sK3,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(sK3,X2,X1)
        | v1_xboole_0(X1)
        | v1_xboole_0(X2) )
    | ~ spl6_8 ),
    inference(resolution,[],[f236,f104])).

fof(f219,plain,
    ( spl6_27
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f205,f164,f129,f112,f102,f92,f87,f82,f77,f72,f67,f216])).

fof(f216,plain,
    ( spl6_27
  <=> k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f67,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f72,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f77,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f82,plain,
    ( spl6_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f87,plain,
    ( spl6_5
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f112,plain,
    ( spl6_10
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f205,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k7_relat_1(sK3,u1_struct_0(sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f203,f189])).

fof(f203,plain,
    ( k2_tmap_1(sK1,sK0,sK3,sK2) = k2_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),sK3,u1_struct_0(sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f84,f89,f94,f69,f74,f79,f104,f114,f131,f166,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f114,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f79,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f74,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f69,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f89,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f84,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f214,plain,
    ( ~ spl6_26
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_19
    | spl6_22 ),
    inference(avatar_split_clause,[],[f206,f179,f164,f129,f112,f102,f92,f87,f82,f77,f72,f67,f211])).

fof(f211,plain,
    ( spl6_26
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f179,plain,
    ( spl6_22
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f206,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k7_relat_1(sK3,u1_struct_0(sK2)),sK4)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | ~ spl6_10
    | ~ spl6_13
    | ~ spl6_19
    | spl6_22 ),
    inference(backward_demodulation,[],[f181,f205])).

fof(f181,plain,
    ( ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f179])).

fof(f202,plain,
    ( spl6_25
    | ~ spl6_9
    | ~ spl6_14
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f192,f174,f134,f107,f199])).

fof(f199,plain,
    ( spl6_25
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f192,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),sK4,sK4)
    | ~ spl6_9
    | ~ spl6_14
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f109,f136,f176,f65])).

% (19945)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(X1,X2,X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(condensation,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f197,plain,
    ( spl6_24
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f191,f164,f129,f102,f194])).

fof(f194,plain,
    ( spl6_24
  <=> r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f191,plain,
    ( r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK3)
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f104,f131,f166,f65])).

fof(f188,plain,
    ( spl6_23
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f183,f112,f92,f185])).

fof(f183,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f94,f114,f58])).

fof(f182,plain,(
    ~ spl6_22 ),
    inference(avatar_split_clause,[],[f52,f179])).

fof(f52,plain,(
    ~ r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK0),k2_tmap_1(sK1,sK0,sK3,sK2),sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f177,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f50,f174])).

fof(f50,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f172,plain,
    ( ~ spl6_20
    | spl6_7
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f152,f148,f97,f169])).

fof(f97,plain,
    ( spl6_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f148,plain,
    ( spl6_16
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f152,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl6_7
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f99,f150,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f150,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f99,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f167,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f47,f164])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f162,plain,
    ( ~ spl6_18
    | spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f145,f124,f82,f159])).

fof(f124,plain,
    ( spl6_12
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

% (19938)Refutation not found, incomplete strategy% (19938)------------------------------
% (19938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19938)Termination reason: Refutation not found, incomplete strategy

% (19938)Memory used [KB]: 10746
% (19938)Time elapsed: 0.094 s
% (19938)------------------------------
% (19938)------------------------------
fof(f145,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl6_4
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f84,f126,f59])).

fof(f126,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f157,plain,
    ( ~ spl6_17
    | spl6_1
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f144,f119,f67,f154])).

fof(f119,plain,
    ( spl6_11
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f144,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f69,f121,f59])).

fof(f121,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f151,plain,
    ( spl6_16
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f146,f140,f148])).

fof(f146,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f142,f56])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f143,plain,
    ( spl6_15
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f138,f112,f92,f140])).

fof(f138,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f94,f114,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f137,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f49,f134])).

fof(f49,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f132,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f46,f129])).

fof(f46,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f127,plain,
    ( spl6_12
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f117,f92,f124])).

fof(f117,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f94,f56])).

fof(f122,plain,
    ( spl6_11
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f116,f77,f119])).

fof(f116,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f79,f56])).

fof(f115,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f44,f112])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f110,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f48,f107])).

fof(f48,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f105,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f45,f102])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f43,f97])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f42,f92])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f41,f87])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f85,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f39,f77])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f38,f72])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f37,f67])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

%------------------------------------------------------------------------------
