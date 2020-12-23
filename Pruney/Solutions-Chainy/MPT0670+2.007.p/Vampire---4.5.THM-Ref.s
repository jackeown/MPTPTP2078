%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 159 expanded)
%              Number of leaves         :   23 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  333 ( 522 expanded)
%              Number of equality atoms :   50 (  78 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f59,f63,f71,f75,f79,f83,f120,f136,f162,f169,f195,f213,f224,f244])).

fof(f244,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_11
    | spl4_33 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_11
    | spl4_33 ),
    inference(subsumption_resolution,[],[f242,f50])).

fof(f50,plain,
    ( r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f242,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_11
    | spl4_33 ),
    inference(subsumption_resolution,[],[f241,f42])).

fof(f42,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f241,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl4_2
    | ~ spl4_11
    | spl4_33 ),
    inference(subsumption_resolution,[],[f239,f46])).

fof(f46,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f239,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))
    | ~ spl4_11
    | spl4_33 ),
    inference(resolution,[],[f209,f82])).

fof(f82,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_11
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f209,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_33
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f224,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10
    | spl4_34 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10
    | spl4_34 ),
    inference(unit_resulting_resolution,[],[f46,f42,f50,f212,f78])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k1_relat_1(X2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_10
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f212,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl4_34
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f213,plain,
    ( ~ spl4_33
    | ~ spl4_34
    | spl4_4
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f202,f193,f53,f211,f208])).

fof(f53,plain,
    ( spl4_4
  <=> k1_funct_1(sK2,sK0) = k1_funct_1(k8_relat_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f193,plain,
    ( spl4_30
  <=> ! [X3,X2] :
        ( k1_funct_1(sK2,X3) = k1_funct_1(k8_relat_1(X2,sK2),X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f202,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl4_4
    | ~ spl4_30 ),
    inference(trivial_inequality_removal,[],[f200])).

fof(f200,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl4_4
    | ~ spl4_30 ),
    inference(superposition,[],[f54,f194])).

fof(f194,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK2,X3) = k1_funct_1(k8_relat_1(X2,sK2),X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X3),X2) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f193])).

fof(f54,plain,
    ( k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f195,plain,
    ( spl4_30
    | ~ spl4_8
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f174,f167,f69,f193])).

fof(f69,plain,
    ( spl4_8
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | k1_funct_1(k6_relat_1(X0),X2) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f167,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,X1)) = k1_funct_1(k8_relat_1(X0,sK2),X1)
        | ~ r2_hidden(X1,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f174,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK2,X3) = k1_funct_1(k8_relat_1(X2,sK2),X3)
        | ~ r2_hidden(X3,k1_relat_1(sK2))
        | ~ r2_hidden(k1_funct_1(sK2,X3),X2) )
    | ~ spl4_8
    | ~ spl4_25 ),
    inference(superposition,[],[f168,f70])).

fof(f70,plain,
    ( ! [X2,X0] :
        ( k1_funct_1(k6_relat_1(X0),X2) = X2
        | ~ r2_hidden(X2,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,X1)) = k1_funct_1(k8_relat_1(X0,sK2),X1)
        | ~ r2_hidden(X1,k1_relat_1(sK2)) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f167])).

fof(f169,plain,
    ( spl4_25
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f165,f160,f73,f41,f167])).

fof(f73,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f160,plain,
    ( spl4_24
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK2))
        | k1_funct_1(k5_relat_1(sK2,k6_relat_1(X1)),X2) = k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,X1)) = k1_funct_1(k8_relat_1(X0,sK2),X1)
        | ~ r2_hidden(X1,k1_relat_1(sK2)) )
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f163,f42])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,X1)) = k1_funct_1(k8_relat_1(X0,sK2),X1)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl4_9
    | ~ spl4_24 ),
    inference(superposition,[],[f161,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
        | ~ v1_relat_1(X1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f161,plain,
    ( ! [X2,X1] :
        ( k1_funct_1(k5_relat_1(sK2,k6_relat_1(X1)),X2) = k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2))
        | ~ r2_hidden(X2,k1_relat_1(sK2)) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl4_24
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f140,f134,f61,f57,f160])).

fof(f57,plain,
    ( spl4_5
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f61,plain,
    ( spl4_6
  <=> ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f134,plain,
    ( spl4_20
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | k1_funct_1(k5_relat_1(sK2,X0),X1) = k1_funct_1(X0,k1_funct_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f140,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k1_relat_1(sK2))
        | k1_funct_1(k5_relat_1(sK2,k6_relat_1(X1)),X2) = k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) )
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f138,f58])).

fof(f58,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f138,plain,
    ( ! [X2,X1] :
        ( ~ v1_relat_1(k6_relat_1(X1))
        | ~ r2_hidden(X2,k1_relat_1(sK2))
        | k1_funct_1(k5_relat_1(sK2,k6_relat_1(X1)),X2) = k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) )
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(resolution,[],[f135,f62])).

fof(f62,plain,
    ( ! [X0] : v1_funct_1(k6_relat_1(X0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | k1_funct_1(k5_relat_1(sK2,X0),X1) = k1_funct_1(X0,k1_funct_1(sK2,X1)) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( spl4_20
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f130,f118,f45,f41,f134])).

fof(f118,plain,
    ( spl4_17
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | k1_funct_1(k5_relat_1(sK2,X0),X1) = k1_funct_1(X0,k1_funct_1(sK2,X1)) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f128,f42])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | k1_funct_1(k5_relat_1(sK2,X0),X1) = k1_funct_1(X0,k1_funct_1(sK2,X1)) )
    | ~ spl4_2
    | ~ spl4_17 ),
    inference(resolution,[],[f119,f46])).

fof(f119,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f28,f118])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

% (12110)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f83,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f30,f81])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X0),X1)
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

fof(f79,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f29,f77])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f23,f73])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f71,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f39,f69])).

fof(f39,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k6_relat_1(X0),X2) = X2 ) ),
    inference(subsumption_resolution,[],[f38,f22])).

fof(f22,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(k6_relat_1(X0))
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k6_relat_1(X0),X2) = X2 ) ),
    inference(subsumption_resolution,[],[f33,f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(k6_relat_1(X0),X2) = X2 ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,X0)
      | k1_funct_1(X1,X2) = X2
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f63,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f22,f61])).

fof(f59,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f21,f57])).

fof(f55,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f20,f53])).

fof(f20,plain,(
    k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
         => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(f51,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (12111)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (12119)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (12109)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (12103)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (12102)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (12111)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f245,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f43,f47,f51,f55,f59,f63,f71,f75,f79,f83,f120,f136,f162,f169,f195,f213,f224,f244])).
% 0.20/0.48  fof(f244,plain,(
% 0.20/0.48    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_11 | spl4_33),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f243])).
% 0.20/0.48  fof(f243,plain,(
% 0.20/0.48    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_11 | spl4_33)),
% 0.20/0.48    inference(subsumption_resolution,[],[f242,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | ~spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    spl4_3 <=> r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.48  fof(f242,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | (~spl4_1 | ~spl4_2 | ~spl4_11 | spl4_33)),
% 0.20/0.48    inference(subsumption_resolution,[],[f241,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    v1_relat_1(sK2) | ~spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    spl4_1 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f241,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | (~spl4_2 | ~spl4_11 | spl4_33)),
% 0.20/0.48    inference(subsumption_resolution,[],[f239,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    v1_funct_1(sK2) | ~spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    spl4_2 <=> v1_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.48  fof(f239,plain,(
% 0.20/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2))) | (~spl4_11 | spl4_33)),
% 0.20/0.48    inference(resolution,[],[f209,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X2,X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) ) | ~spl4_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f81])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    spl4_11 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl4_33),
% 0.20/0.48    inference(avatar_component_clause,[],[f208])).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    spl4_33 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.20/0.48  fof(f224,plain,(
% 0.20/0.48    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_10 | spl4_34),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f220])).
% 0.20/0.48  fof(f220,plain,(
% 0.20/0.48    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_10 | spl4_34)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f46,f42,f50,f212,f78])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) ) | ~spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl4_10 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.48  fof(f212,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl4_34),
% 0.20/0.48    inference(avatar_component_clause,[],[f211])).
% 0.20/0.48  fof(f211,plain,(
% 0.20/0.48    spl4_34 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.20/0.48  fof(f213,plain,(
% 0.20/0.48    ~spl4_33 | ~spl4_34 | spl4_4 | ~spl4_30),
% 0.20/0.48    inference(avatar_split_clause,[],[f202,f193,f53,f211,f208])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl4_4 <=> k1_funct_1(sK2,sK0) = k1_funct_1(k8_relat_1(sK1,sK2),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    spl4_30 <=> ! [X3,X2] : (k1_funct_1(sK2,X3) = k1_funct_1(k8_relat_1(X2,sK2),X3) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,X3),X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | (spl4_4 | ~spl4_30)),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f200])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    k1_funct_1(sK2,sK0) != k1_funct_1(sK2,sK0) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | (spl4_4 | ~spl4_30)),
% 0.20/0.48    inference(superposition,[],[f54,f194])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    ( ! [X2,X3] : (k1_funct_1(sK2,X3) = k1_funct_1(k8_relat_1(X2,sK2),X3) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,X3),X2)) ) | ~spl4_30),
% 0.20/0.48    inference(avatar_component_clause,[],[f193])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0) | spl4_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f53])).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    spl4_30 | ~spl4_8 | ~spl4_25),
% 0.20/0.48    inference(avatar_split_clause,[],[f174,f167,f69,f193])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    spl4_8 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | k1_funct_1(k6_relat_1(X0),X2) = X2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.48  fof(f167,plain,(
% 0.20/0.48    spl4_25 <=> ! [X1,X0] : (k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,X1)) = k1_funct_1(k8_relat_1(X0,sK2),X1) | ~r2_hidden(X1,k1_relat_1(sK2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ( ! [X2,X3] : (k1_funct_1(sK2,X3) = k1_funct_1(k8_relat_1(X2,sK2),X3) | ~r2_hidden(X3,k1_relat_1(sK2)) | ~r2_hidden(k1_funct_1(sK2,X3),X2)) ) | (~spl4_8 | ~spl4_25)),
% 0.20/0.48    inference(superposition,[],[f168,f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X2,X0] : (k1_funct_1(k6_relat_1(X0),X2) = X2 | ~r2_hidden(X2,X0)) ) | ~spl4_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f69])).
% 0.20/0.48  fof(f168,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,X1)) = k1_funct_1(k8_relat_1(X0,sK2),X1) | ~r2_hidden(X1,k1_relat_1(sK2))) ) | ~spl4_25),
% 0.20/0.48    inference(avatar_component_clause,[],[f167])).
% 0.20/0.48  fof(f169,plain,(
% 0.20/0.48    spl4_25 | ~spl4_1 | ~spl4_9 | ~spl4_24),
% 0.20/0.48    inference(avatar_split_clause,[],[f165,f160,f73,f41,f167])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    spl4_9 <=> ! [X1,X0] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    spl4_24 <=> ! [X1,X2] : (~r2_hidden(X2,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK2,k6_relat_1(X1)),X2) = k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.48  fof(f165,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,X1)) = k1_funct_1(k8_relat_1(X0,sK2),X1) | ~r2_hidden(X1,k1_relat_1(sK2))) ) | (~spl4_1 | ~spl4_9 | ~spl4_24)),
% 0.20/0.48    inference(subsumption_resolution,[],[f163,f42])).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_funct_1(k6_relat_1(X0),k1_funct_1(sK2,X1)) = k1_funct_1(k8_relat_1(X0,sK2),X1) | ~r2_hidden(X1,k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | (~spl4_9 | ~spl4_24)),
% 0.20/0.48    inference(superposition,[],[f161,f74])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) ) | ~spl4_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f73])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    ( ! [X2,X1] : (k1_funct_1(k5_relat_1(sK2,k6_relat_1(X1)),X2) = k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2)) | ~r2_hidden(X2,k1_relat_1(sK2))) ) | ~spl4_24),
% 0.20/0.48    inference(avatar_component_clause,[],[f160])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    spl4_24 | ~spl4_5 | ~spl4_6 | ~spl4_20),
% 0.20/0.48    inference(avatar_split_clause,[],[f140,f134,f61,f57,f160])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl4_5 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl4_6 <=> ! [X0] : v1_funct_1(k6_relat_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    spl4_20 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK2,X0),X1) = k1_funct_1(X0,k1_funct_1(sK2,X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~r2_hidden(X2,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK2,k6_relat_1(X1)),X2) = k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2))) ) | (~spl4_5 | ~spl4_6 | ~spl4_20)),
% 0.20/0.48    inference(subsumption_resolution,[],[f138,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl4_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f57])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | ~r2_hidden(X2,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK2,k6_relat_1(X1)),X2) = k1_funct_1(k6_relat_1(X1),k1_funct_1(sK2,X2))) ) | (~spl4_6 | ~spl4_20)),
% 0.20/0.48    inference(resolution,[],[f135,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) ) | ~spl4_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f61])).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK2,X0),X1) = k1_funct_1(X0,k1_funct_1(sK2,X1))) ) | ~spl4_20),
% 0.20/0.48    inference(avatar_component_clause,[],[f134])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    spl4_20 | ~spl4_1 | ~spl4_2 | ~spl4_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f130,f118,f45,f41,f134])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    spl4_17 <=> ! [X1,X0,X2] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK2,X0),X1) = k1_funct_1(X0,k1_funct_1(sK2,X1))) ) | (~spl4_1 | ~spl4_2 | ~spl4_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f128,f42])).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(sK2)) | k1_funct_1(k5_relat_1(sK2,X0),X1) = k1_funct_1(X0,k1_funct_1(sK2,X1))) ) | (~spl4_2 | ~spl4_17)),
% 0.20/0.48    inference(resolution,[],[f119,f46])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) ) | ~spl4_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f118])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl4_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f28,f118])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  % (12110)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl4_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f30,f81])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(k1_funct_1(X2,X0),X1) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(k1_funct_1(X2,X0),X1) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    spl4_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f77])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl4_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f23,f73])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    spl4_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f69])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_funct_1(k6_relat_1(X0),X2) = X2) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f38,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~v1_funct_1(k6_relat_1(X0)) | ~r2_hidden(X2,X0) | k1_funct_1(k6_relat_1(X0),X2) = X2) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f33,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0] : (~v1_relat_1(k6_relat_1(X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~r2_hidden(X2,X0) | k1_funct_1(k6_relat_1(X0),X2) = X2) )),
% 0.20/0.48    inference(equality_resolution,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,X0) | k1_funct_1(X1,X2) = X2 | k6_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl4_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f22,f61])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    spl4_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f57])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ~spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f20,f53])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    k1_funct_1(sK2,sK0) != k1_funct_1(k8_relat_1(sK1,sK2),sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f19,f49])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    r2_hidden(sK0,k1_relat_1(k8_relat_1(sK1,sK2)))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f18,f45])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    spl4_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f17,f41])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (12111)------------------------------
% 0.20/0.48  % (12111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (12111)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (12111)Memory used [KB]: 10746
% 0.20/0.48  % (12111)Time elapsed: 0.071 s
% 0.20/0.48  % (12111)------------------------------
% 0.20/0.48  % (12111)------------------------------
% 0.20/0.49  % (12101)Success in time 0.128 s
%------------------------------------------------------------------------------
