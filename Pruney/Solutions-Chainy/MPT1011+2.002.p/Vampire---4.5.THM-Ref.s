%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:20 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 203 expanded)
%              Number of leaves         :   23 (  86 expanded)
%              Depth                    :   12
%              Number of atoms          :  389 ( 756 expanded)
%              Number of equality atoms :   44 (  58 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f279,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f90,f159,f180,f197,f229,f254,f258,f262,f269,f277,f278])).

fof(f278,plain,
    ( sK1 != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | sK1 != k1_funct_1(sK2,sK4(sK0,sK2,sK3))
    | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) = k1_funct_1(sK3,sK4(sK0,sK2,sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f277,plain,
    ( spl6_35
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f270,f260,f275])).

fof(f275,plain,
    ( spl6_35
  <=> sK1 = k1_funct_1(sK3,sK4(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f260,plain,
    ( spl6_33
  <=> r2_hidden(k1_funct_1(sK3,sK4(sK0,sK2,sK3)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f270,plain,
    ( sK1 = k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | ~ spl6_33 ),
    inference(resolution,[],[f261,f58])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f261,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4(sK0,sK2,sK3)),k1_tarski(sK1))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f260])).

fof(f269,plain,
    ( spl6_34
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f264,f256,f267])).

fof(f267,plain,
    ( spl6_34
  <=> sK1 = k1_funct_1(sK2,sK4(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f256,plain,
    ( spl6_32
  <=> r2_hidden(k1_funct_1(sK2,sK4(sK0,sK2,sK3)),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f264,plain,
    ( sK1 = k1_funct_1(sK2,sK4(sK0,sK2,sK3))
    | ~ spl6_32 ),
    inference(resolution,[],[f257,f58])).

fof(f257,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(sK0,sK2,sK3)),k1_tarski(sK1))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f256])).

fof(f262,plain,
    ( spl6_33
    | ~ spl6_18
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f239,f227,f157,f260])).

fof(f157,plain,
    ( spl6_18
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f227,plain,
    ( spl6_27
  <=> r2_hidden(sK4(sK0,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f239,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4(sK0,sK2,sK3)),k1_tarski(sK1))
    | ~ spl6_18
    | ~ spl6_27 ),
    inference(resolution,[],[f228,f158])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f157])).

fof(f228,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f227])).

fof(f258,plain,
    ( spl6_32
    | ~ spl6_24
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f238,f227,f195,f256])).

fof(f195,plain,
    ( spl6_24
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f238,plain,
    ( r2_hidden(k1_funct_1(sK2,sK4(sK0,sK2,sK3)),k1_tarski(sK1))
    | ~ spl6_24
    | ~ spl6_27 ),
    inference(resolution,[],[f228,f196])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK1)) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f195])).

fof(f254,plain,
    ( ~ spl6_31
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f235,f88,f84,f80,f76,f72,f68,f64,f252])).

fof(f252,plain,
    ( spl6_31
  <=> k1_funct_1(sK2,sK4(sK0,sK2,sK3)) = k1_funct_1(sK3,sK4(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f64,plain,
    ( spl6_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f68,plain,
    ( spl6_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f72,plain,
    ( spl6_3
  <=> v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f76,plain,
    ( spl6_4
  <=> v1_funct_2(sK2,sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f80,plain,
    ( spl6_5
  <=> r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f84,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f88,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f235,plain,
    ( k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f234,f81])).

fof(f81,plain,
    ( ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f234,plain,
    ( k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f233,f65])).

fof(f65,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f233,plain,
    ( ~ v1_funct_1(sK3)
    | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f230,f73])).

fof(f73,plain,
    ( v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f230,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK3)
    | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3))
    | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(resolution,[],[f114,f85])).

fof(f85,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f114,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_2(X2,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(X2)
        | k1_funct_1(sK2,sK4(sK0,sK2,X2)) != k1_funct_1(X2,sK4(sK0,sK2,X2))
        | r2_relset_1(sK0,k1_tarski(sK1),sK2,X2) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f113,f69])).

fof(f69,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f113,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k1_funct_1(sK2,sK4(sK0,sK2,X2)) != k1_funct_1(X2,sK4(sK0,sK2,X2))
        | r2_relset_1(sK0,k1_tarski(sK1),sK2,X2) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f105,f77])).

fof(f77,plain,
    ( v1_funct_2(sK2,sK0,k1_tarski(sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f105,plain,
    ( ! [X2] :
        ( ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | k1_funct_1(sK2,sK4(sK0,sK2,X2)) != k1_funct_1(X2,sK4(sK0,sK2,X2))
        | r2_relset_1(sK0,k1_tarski(sK1),sK2,X2) )
    | ~ spl6_7 ),
    inference(resolution,[],[f89,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3))
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f89,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f229,plain,
    ( spl6_27
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f218,f88,f84,f80,f76,f72,f68,f64,f227])).

fof(f218,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f217,f81])).

fof(f217,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f216,f65])).

fof(f216,plain,
    ( ~ v1_funct_1(sK3)
    | r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f214,f73])).

fof(f214,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
    | ~ v1_funct_1(sK3)
    | r2_hidden(sK4(sK0,sK2,sK3),sK0)
    | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7 ),
    inference(resolution,[],[f112,f85])).

fof(f112,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | ~ v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(X1)
        | r2_hidden(sK4(sK0,sK2,X1),sK0)
        | r2_relset_1(sK0,k1_tarski(sK1),sK2,X1) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f111,f69])).

fof(f111,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r2_hidden(sK4(sK0,sK2,X1),sK0)
        | r2_relset_1(sK0,k1_tarski(sK1),sK2,X1) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f104,f77])).

fof(f104,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK0,k1_tarski(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))
        | r2_hidden(sK4(sK0,sK2,X1),sK0)
        | r2_relset_1(sK0,k1_tarski(sK1),sK2,X1) )
    | ~ spl6_7 ),
    inference(resolution,[],[f89,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X2,X3),X0)
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f197,plain,
    ( spl6_17
    | spl6_24
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f110,f88,f76,f68,f195,f154])).

fof(f154,plain,
    ( spl6_17
  <=> k1_xboole_0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = k1_tarski(sK1)
        | r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK1)) )
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f109,f69])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = k1_tarski(sK1)
        | r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK1)) )
    | ~ spl6_4
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f103,f77])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = k1_tarski(sK1)
        | r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK1)) )
    | ~ spl6_7 ),
    inference(resolution,[],[f89,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f180,plain,(
    ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f178,f52])).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f178,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_17 ),
    inference(superposition,[],[f57,f155])).

fof(f155,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f57,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f159,plain,
    ( spl6_17
    | spl6_18
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f98,f84,f72,f64,f157,f154])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = k1_tarski(sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) )
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f97,f65])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = k1_tarski(sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) )
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f91,f73])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK0,k1_tarski(sK1))
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,sK0)
        | k1_xboole_0 = k1_tarski(sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f85,f40])).

fof(f90,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f35,f88])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,k1_tarski(X1),X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X2,X0,k1_tarski(X1))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X2,X0,k1_tarski(X1))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
              & v1_funct_2(X3,X0,k1_tarski(X1))
              & v1_funct_1(X3) )
           => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X2,X0,k1_tarski(X1))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
            & v1_funct_2(X3,X0,k1_tarski(X1))
            & v1_funct_1(X3) )
         => r2_relset_1(X0,k1_tarski(X1),X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).

fof(f86,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f31,f84])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f32,f80])).

fof(f32,plain,(
    ~ r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f34,f76])).

fof(f34,plain,(
    v1_funct_2(sK2,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f30,f72])).

fof(f30,plain,(
    v1_funct_2(sK3,sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:40:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.46  % (15907)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.50  % (15929)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.50  % (15914)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.52  % (15929)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.53  % (15916)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f279,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(avatar_sat_refutation,[],[f66,f70,f74,f78,f82,f86,f90,f159,f180,f197,f229,f254,f258,f262,f269,f277,f278])).
% 0.23/0.53  fof(f278,plain,(
% 0.23/0.53    sK1 != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | sK1 != k1_funct_1(sK2,sK4(sK0,sK2,sK3)) | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) = k1_funct_1(sK3,sK4(sK0,sK2,sK3))),
% 0.23/0.53    introduced(theory_tautology_sat_conflict,[])).
% 0.23/0.53  fof(f277,plain,(
% 0.23/0.53    spl6_35 | ~spl6_33),
% 0.23/0.53    inference(avatar_split_clause,[],[f270,f260,f275])).
% 0.23/0.53  fof(f275,plain,(
% 0.23/0.53    spl6_35 <=> sK1 = k1_funct_1(sK3,sK4(sK0,sK2,sK3))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.23/0.53  fof(f260,plain,(
% 0.23/0.53    spl6_33 <=> r2_hidden(k1_funct_1(sK3,sK4(sK0,sK2,sK3)),k1_tarski(sK1))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.23/0.53  fof(f270,plain,(
% 0.23/0.53    sK1 = k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | ~spl6_33),
% 0.23/0.53    inference(resolution,[],[f261,f58])).
% 0.23/0.53  fof(f58,plain,(
% 0.23/0.53    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.23/0.53    inference(equality_resolution,[],[f44])).
% 0.23/0.53  fof(f44,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.23/0.53    inference(cnf_transformation,[],[f5])).
% 0.23/0.53  fof(f5,axiom,(
% 0.23/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.23/0.53  fof(f261,plain,(
% 0.23/0.53    r2_hidden(k1_funct_1(sK3,sK4(sK0,sK2,sK3)),k1_tarski(sK1)) | ~spl6_33),
% 0.23/0.53    inference(avatar_component_clause,[],[f260])).
% 0.23/0.53  fof(f269,plain,(
% 0.23/0.53    spl6_34 | ~spl6_32),
% 0.23/0.53    inference(avatar_split_clause,[],[f264,f256,f267])).
% 0.23/0.53  fof(f267,plain,(
% 0.23/0.53    spl6_34 <=> sK1 = k1_funct_1(sK2,sK4(sK0,sK2,sK3))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.23/0.53  fof(f256,plain,(
% 0.23/0.53    spl6_32 <=> r2_hidden(k1_funct_1(sK2,sK4(sK0,sK2,sK3)),k1_tarski(sK1))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.23/0.53  fof(f264,plain,(
% 0.23/0.53    sK1 = k1_funct_1(sK2,sK4(sK0,sK2,sK3)) | ~spl6_32),
% 0.23/0.53    inference(resolution,[],[f257,f58])).
% 0.23/0.53  fof(f257,plain,(
% 0.23/0.53    r2_hidden(k1_funct_1(sK2,sK4(sK0,sK2,sK3)),k1_tarski(sK1)) | ~spl6_32),
% 0.23/0.53    inference(avatar_component_clause,[],[f256])).
% 0.23/0.53  fof(f262,plain,(
% 0.23/0.53    spl6_33 | ~spl6_18 | ~spl6_27),
% 0.23/0.53    inference(avatar_split_clause,[],[f239,f227,f157,f260])).
% 0.23/0.53  fof(f157,plain,(
% 0.23/0.53    spl6_18 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1)))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.23/0.53  fof(f227,plain,(
% 0.23/0.53    spl6_27 <=> r2_hidden(sK4(sK0,sK2,sK3),sK0)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.23/0.53  fof(f239,plain,(
% 0.23/0.53    r2_hidden(k1_funct_1(sK3,sK4(sK0,sK2,sK3)),k1_tarski(sK1)) | (~spl6_18 | ~spl6_27)),
% 0.23/0.53    inference(resolution,[],[f228,f158])).
% 0.23/0.53  fof(f158,plain,(
% 0.23/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))) ) | ~spl6_18),
% 0.23/0.53    inference(avatar_component_clause,[],[f157])).
% 0.23/0.53  fof(f228,plain,(
% 0.23/0.53    r2_hidden(sK4(sK0,sK2,sK3),sK0) | ~spl6_27),
% 0.23/0.53    inference(avatar_component_clause,[],[f227])).
% 0.23/0.53  fof(f258,plain,(
% 0.23/0.53    spl6_32 | ~spl6_24 | ~spl6_27),
% 0.23/0.53    inference(avatar_split_clause,[],[f238,f227,f195,f256])).
% 0.23/0.53  fof(f195,plain,(
% 0.23/0.53    spl6_24 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK1)))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.23/0.53  fof(f238,plain,(
% 0.23/0.53    r2_hidden(k1_funct_1(sK2,sK4(sK0,sK2,sK3)),k1_tarski(sK1)) | (~spl6_24 | ~spl6_27)),
% 0.23/0.53    inference(resolution,[],[f228,f196])).
% 0.23/0.53  fof(f196,plain,(
% 0.23/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK1))) ) | ~spl6_24),
% 0.23/0.53    inference(avatar_component_clause,[],[f195])).
% 0.23/0.53  fof(f254,plain,(
% 0.23/0.53    ~spl6_31 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_7),
% 0.23/0.53    inference(avatar_split_clause,[],[f235,f88,f84,f80,f76,f72,f68,f64,f252])).
% 0.23/0.53  fof(f252,plain,(
% 0.23/0.53    spl6_31 <=> k1_funct_1(sK2,sK4(sK0,sK2,sK3)) = k1_funct_1(sK3,sK4(sK0,sK2,sK3))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.23/0.53  fof(f64,plain,(
% 0.23/0.53    spl6_1 <=> v1_funct_1(sK3)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.23/0.53  fof(f68,plain,(
% 0.23/0.53    spl6_2 <=> v1_funct_1(sK2)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.23/0.53  fof(f72,plain,(
% 0.23/0.53    spl6_3 <=> v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.23/0.53  fof(f76,plain,(
% 0.23/0.53    spl6_4 <=> v1_funct_2(sK2,sK0,k1_tarski(sK1))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.23/0.53  fof(f80,plain,(
% 0.23/0.53    spl6_5 <=> r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.23/0.53  fof(f84,plain,(
% 0.23/0.53    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.23/0.53  fof(f88,plain,(
% 0.23/0.53    spl6_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.23/0.53  fof(f235,plain,(
% 0.23/0.53    k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f234,f81])).
% 0.23/0.53  fof(f81,plain,(
% 0.23/0.53    ~r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) | spl6_5),
% 0.23/0.53    inference(avatar_component_clause,[],[f80])).
% 0.23/0.53  fof(f234,plain,(
% 0.23/0.53    k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f233,f65])).
% 0.23/0.53  fof(f65,plain,(
% 0.23/0.53    v1_funct_1(sK3) | ~spl6_1),
% 0.23/0.53    inference(avatar_component_clause,[],[f64])).
% 0.23/0.53  fof(f233,plain,(
% 0.23/0.53    ~v1_funct_1(sK3) | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f230,f73])).
% 0.23/0.53  fof(f73,plain,(
% 0.23/0.53    v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~spl6_3),
% 0.23/0.53    inference(avatar_component_clause,[],[f72])).
% 0.23/0.53  fof(f230,plain,(
% 0.23/0.53    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | k1_funct_1(sK2,sK4(sK0,sK2,sK3)) != k1_funct_1(sK3,sK4(sK0,sK2,sK3)) | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) | (~spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7)),
% 0.23/0.53    inference(resolution,[],[f114,f85])).
% 0.23/0.53  fof(f85,plain,(
% 0.23/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_6),
% 0.23/0.53    inference(avatar_component_clause,[],[f84])).
% 0.23/0.53  fof(f114,plain,(
% 0.23/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_2(X2,sK0,k1_tarski(sK1)) | ~v1_funct_1(X2) | k1_funct_1(sK2,sK4(sK0,sK2,X2)) != k1_funct_1(X2,sK4(sK0,sK2,X2)) | r2_relset_1(sK0,k1_tarski(sK1),sK2,X2)) ) | (~spl6_2 | ~spl6_4 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f113,f69])).
% 0.23/0.53  fof(f69,plain,(
% 0.23/0.53    v1_funct_1(sK2) | ~spl6_2),
% 0.23/0.53    inference(avatar_component_clause,[],[f68])).
% 0.23/0.53  fof(f113,plain,(
% 0.23/0.53    ( ! [X2] : (~v1_funct_1(sK2) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK0,k1_tarski(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_funct_1(sK2,sK4(sK0,sK2,X2)) != k1_funct_1(X2,sK4(sK0,sK2,X2)) | r2_relset_1(sK0,k1_tarski(sK1),sK2,X2)) ) | (~spl6_4 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f105,f77])).
% 0.23/0.53  fof(f77,plain,(
% 0.23/0.53    v1_funct_2(sK2,sK0,k1_tarski(sK1)) | ~spl6_4),
% 0.23/0.53    inference(avatar_component_clause,[],[f76])).
% 0.23/0.53  fof(f105,plain,(
% 0.23/0.53    ( ! [X2] : (~v1_funct_2(sK2,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_1(X2) | ~v1_funct_2(X2,sK0,k1_tarski(sK1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | k1_funct_1(sK2,sK4(sK0,sK2,X2)) != k1_funct_1(X2,sK4(sK0,sK2,X2)) | r2_relset_1(sK0,k1_tarski(sK1),sK2,X2)) ) | ~spl6_7),
% 0.23/0.53    inference(resolution,[],[f89,f37])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_funct_1(X2,sK4(X0,X2,X3)) != k1_funct_1(X3,sK4(X0,X2,X3)) | r2_relset_1(X0,X1,X2,X3)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (! [X3] : (r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.23/0.53    inference(flattening,[],[f23])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ! [X0,X1,X2] : (! [X3] : ((r2_relset_1(X0,X1,X2,X3) | ? [X4] : (k1_funct_1(X2,X4) != k1_funct_1(X3,X4) & r2_hidden(X4,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.23/0.53    inference(ennf_transformation,[],[f17])).
% 0.23/0.53  fof(f17,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.23/0.53  fof(f89,plain,(
% 0.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~spl6_7),
% 0.23/0.53    inference(avatar_component_clause,[],[f88])).
% 0.23/0.53  fof(f229,plain,(
% 0.23/0.53    spl6_27 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_7),
% 0.23/0.53    inference(avatar_split_clause,[],[f218,f88,f84,f80,f76,f72,f68,f64,f227])).
% 0.23/0.53  fof(f218,plain,(
% 0.23/0.53    r2_hidden(sK4(sK0,sK2,sK3),sK0) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f217,f81])).
% 0.23/0.53  fof(f217,plain,(
% 0.23/0.53    r2_hidden(sK4(sK0,sK2,sK3),sK0) | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f216,f65])).
% 0.23/0.53  fof(f216,plain,(
% 0.23/0.53    ~v1_funct_1(sK3) | r2_hidden(sK4(sK0,sK2,sK3),sK0) | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_6 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f214,f73])).
% 0.23/0.53  fof(f214,plain,(
% 0.23/0.53    ~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | r2_hidden(sK4(sK0,sK2,sK3),sK0) | r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3) | (~spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7)),
% 0.23/0.53    inference(resolution,[],[f112,f85])).
% 0.23/0.53  fof(f112,plain,(
% 0.23/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | ~v1_funct_2(X1,sK0,k1_tarski(sK1)) | ~v1_funct_1(X1) | r2_hidden(sK4(sK0,sK2,X1),sK0) | r2_relset_1(sK0,k1_tarski(sK1),sK2,X1)) ) | (~spl6_2 | ~spl6_4 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f111,f69])).
% 0.23/0.53  fof(f111,plain,(
% 0.23/0.53    ( ! [X1] : (~v1_funct_1(sK2) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,k1_tarski(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK4(sK0,sK2,X1),sK0) | r2_relset_1(sK0,k1_tarski(sK1),sK2,X1)) ) | (~spl6_4 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f104,f77])).
% 0.23/0.53  fof(f104,plain,(
% 0.23/0.53    ( ! [X1] : (~v1_funct_2(sK2,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK0,k1_tarski(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1)))) | r2_hidden(sK4(sK0,sK2,X1),sK0) | r2_relset_1(sK0,k1_tarski(sK1),sK2,X1)) ) | ~spl6_7),
% 0.23/0.53    inference(resolution,[],[f89,f36])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X2,X3),X0) | r2_relset_1(X0,X1,X2,X3)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f24])).
% 0.23/0.53  fof(f197,plain,(
% 0.23/0.53    spl6_17 | spl6_24 | ~spl6_2 | ~spl6_4 | ~spl6_7),
% 0.23/0.53    inference(avatar_split_clause,[],[f110,f88,f76,f68,f195,f154])).
% 0.23/0.53  fof(f154,plain,(
% 0.23/0.53    spl6_17 <=> k1_xboole_0 = k1_tarski(sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.23/0.53  fof(f110,plain,(
% 0.23/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k1_tarski(sK1) | r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK1))) ) | (~spl6_2 | ~spl6_4 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f109,f69])).
% 0.23/0.53  fof(f109,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_funct_1(sK2) | ~r2_hidden(X0,sK0) | k1_xboole_0 = k1_tarski(sK1) | r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK1))) ) | (~spl6_4 | ~spl6_7)),
% 0.23/0.53    inference(subsumption_resolution,[],[f103,f77])).
% 0.23/0.53  fof(f103,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_funct_2(sK2,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK2) | ~r2_hidden(X0,sK0) | k1_xboole_0 = k1_tarski(sK1) | r2_hidden(k1_funct_1(sK2,X0),k1_tarski(sK1))) ) | ~spl6_7),
% 0.23/0.53    inference(resolution,[],[f89,f40])).
% 0.23/0.53  fof(f40,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f26])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.23/0.53    inference(flattening,[],[f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.23/0.53    inference(ennf_transformation,[],[f18])).
% 0.23/0.53  fof(f18,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.23/0.53  fof(f180,plain,(
% 0.23/0.53    ~spl6_17),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f179])).
% 0.23/0.53  fof(f179,plain,(
% 0.23/0.53    $false | ~spl6_17),
% 0.23/0.53    inference(subsumption_resolution,[],[f178,f52])).
% 0.23/0.53  fof(f52,plain,(
% 0.23/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.53    inference(cnf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.53  fof(f178,plain,(
% 0.23/0.53    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl6_17),
% 0.23/0.53    inference(superposition,[],[f57,f155])).
% 0.23/0.53  fof(f155,plain,(
% 0.23/0.53    k1_xboole_0 = k1_tarski(sK1) | ~spl6_17),
% 0.23/0.53    inference(avatar_component_clause,[],[f154])).
% 0.23/0.53  fof(f57,plain,(
% 0.23/0.53    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.23/0.53    inference(equality_resolution,[],[f42])).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f13])).
% 0.23/0.53  fof(f13,axiom,(
% 0.23/0.53    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.23/0.53  fof(f159,plain,(
% 0.23/0.53    spl6_17 | spl6_18 | ~spl6_1 | ~spl6_3 | ~spl6_6),
% 0.23/0.53    inference(avatar_split_clause,[],[f98,f84,f72,f64,f157,f154])).
% 0.23/0.53  fof(f98,plain,(
% 0.23/0.53    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = k1_tarski(sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))) ) | (~spl6_1 | ~spl6_3 | ~spl6_6)),
% 0.23/0.53    inference(subsumption_resolution,[],[f97,f65])).
% 0.23/0.53  fof(f97,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_funct_1(sK3) | ~r2_hidden(X0,sK0) | k1_xboole_0 = k1_tarski(sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))) ) | (~spl6_3 | ~spl6_6)),
% 0.23/0.53    inference(subsumption_resolution,[],[f91,f73])).
% 0.23/0.53  fof(f91,plain,(
% 0.23/0.53    ( ! [X0] : (~v1_funct_2(sK3,sK0,k1_tarski(sK1)) | ~v1_funct_1(sK3) | ~r2_hidden(X0,sK0) | k1_xboole_0 = k1_tarski(sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_tarski(sK1))) ) | ~spl6_6),
% 0.23/0.53    inference(resolution,[],[f85,f40])).
% 0.23/0.53  fof(f90,plain,(
% 0.23/0.53    spl6_7),
% 0.23/0.53    inference(avatar_split_clause,[],[f35,f88])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,k1_tarski(X1),X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2))),
% 0.23/0.53    inference(flattening,[],[f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,k1_tarski(X1),X2,X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)))),
% 0.23/0.53    inference(ennf_transformation,[],[f20])).
% 0.23/0.53  fof(f20,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => r2_relset_1(X0,k1_tarski(X1),X2,X3)))),
% 0.23/0.53    inference(negated_conjecture,[],[f19])).
% 0.23/0.53  fof(f19,conjecture,(
% 0.23/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X2,X0,k1_tarski(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => r2_relset_1(X0,k1_tarski(X1),X2,X3)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_2)).
% 0.23/0.53  fof(f86,plain,(
% 0.23/0.53    spl6_6),
% 0.23/0.53    inference(avatar_split_clause,[],[f31,f84])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_tarski(sK1))))),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f82,plain,(
% 0.23/0.53    ~spl6_5),
% 0.23/0.53    inference(avatar_split_clause,[],[f32,f80])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ~r2_relset_1(sK0,k1_tarski(sK1),sK2,sK3)),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f78,plain,(
% 0.23/0.53    spl6_4),
% 0.23/0.53    inference(avatar_split_clause,[],[f34,f76])).
% 0.23/0.53  fof(f34,plain,(
% 0.23/0.53    v1_funct_2(sK2,sK0,k1_tarski(sK1))),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f74,plain,(
% 0.23/0.53    spl6_3),
% 0.23/0.53    inference(avatar_split_clause,[],[f30,f72])).
% 0.23/0.53  fof(f30,plain,(
% 0.23/0.53    v1_funct_2(sK3,sK0,k1_tarski(sK1))),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f70,plain,(
% 0.23/0.53    spl6_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f33,f68])).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    v1_funct_1(sK2)),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    spl6_1),
% 0.23/0.53    inference(avatar_split_clause,[],[f29,f64])).
% 0.23/0.53  fof(f29,plain,(
% 0.23/0.53    v1_funct_1(sK3)),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (15929)------------------------------
% 0.23/0.53  % (15929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (15929)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (15929)Memory used [KB]: 6396
% 0.23/0.53  % (15929)Time elapsed: 0.113 s
% 0.23/0.53  % (15929)------------------------------
% 0.23/0.53  % (15929)------------------------------
% 0.23/0.53  % (15902)Success in time 0.168 s
%------------------------------------------------------------------------------
