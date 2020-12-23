%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 446 expanded)
%              Number of leaves         :   36 ( 189 expanded)
%              Depth                    :   17
%              Number of atoms          : 1128 (1866 expanded)
%              Number of equality atoms :   78 ( 118 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f389,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f99,f104,f111,f116,f122,f140,f166,f197,f213,f228,f241,f256,f274,f289,f334,f341,f352,f373,f374,f388])).

fof(f388,plain,
    ( spl7_2
    | spl7_3
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | spl7_2
    | spl7_3
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f386,f74])).

fof(f74,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f386,plain,
    ( v1_xboole_0(sK1)
    | spl7_2
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f385,f69])).

fof(f69,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl7_2
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f385,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f224,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

% (2989)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

fof(f224,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl7_16
  <=> v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f374,plain,
    ( k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4) != k1_mcart_1(k1_funct_1(sK3,sK4))
    | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) != k2_mcart_1(k1_funct_1(sK3,sK4))
    | k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k1_funct_1(sK3,sK4)),k2_mcart_1(k1_funct_1(sK3,sK4)))
    | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k1_funct_1(sK3,sK4)
    | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f373,plain,
    ( spl7_30
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f325,f276,f238,f194,f137,f101,f96,f82,f77,f72,f67,f62,f370])).

fof(f370,plain,
    ( spl7_30
  <=> k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4) = k1_mcart_1(k1_funct_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f62,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f77,plain,
    ( spl7_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f82,plain,
    ( spl7_5
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f96,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f101,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f137,plain,
    ( spl7_11
  <=> v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f194,plain,
    ( spl7_13
  <=> m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f238,plain,
    ( spl7_19
  <=> k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k1_funct_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f276,plain,
    ( spl7_22
  <=> v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f325,plain,
    ( k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4) = k1_mcart_1(k1_funct_1(sK3,sK4))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_19
    | ~ spl7_22 ),
    inference(forward_demodulation,[],[f322,f240])).

fof(f240,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k1_funct_1(sK3,sK4)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f238])).

fof(f322,plain,
    ( k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(resolution,[],[f321,f84])).

fof(f84,plain,
    ( m1_subset_1(sK4,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_13
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f320,f196])).

fof(f196,plain,
    ( m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f194])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_11
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f161,f277])).

fof(f277,plain,
    ( v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f276])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | ~ m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f160,f79])).

fof(f79,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f160,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | ~ m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f159,f103])).

fof(f103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | ~ m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f158,f98])).

fof(f98,plain,
    ( v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | ~ m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f157,f64])).

fof(f64,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f62])).

% (2990)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f157,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | ~ m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) )
    | spl7_2
    | spl7_3
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f156,f69])).

fof(f156,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | ~ m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) )
    | spl7_3
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f146,f74])).

fof(f146,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
        | ~ m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,sK0)
        | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_11 ),
    inference(resolution,[],[f139,f60])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(k4_funct_2(X0,X1,X2,X3))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(X0)
      | ~ v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
      | ~ m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,X0)
      | k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) = k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,X0)
      | k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
      | k4_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                        & v1_funct_2(X4,X0,X1)
                        & v1_funct_1(X4) )
                     => ( k4_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_funct_2)).

fof(f139,plain,
    ( v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f352,plain,
    ( spl7_28
    | ~ spl7_5
    | ~ spl7_19
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f345,f328,f238,f82,f349])).

fof(f349,plain,
    ( spl7_28
  <=> k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) = k2_mcart_1(k1_funct_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f328,plain,
    ( spl7_26
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f345,plain,
    ( k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) = k2_mcart_1(k1_funct_1(sK3,sK4))
    | ~ spl7_5
    | ~ spl7_19
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f342,f240])).

fof(f342,plain,
    ( k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4))
    | ~ spl7_5
    | ~ spl7_26 ),
    inference(resolution,[],[f329,f84])).

fof(f329,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f328])).

fof(f341,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | spl7_27 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | spl7_27 ),
    inference(subsumption_resolution,[],[f339,f74])).

fof(f339,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | spl7_27 ),
    inference(subsumption_resolution,[],[f338,f103])).

fof(f338,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | v1_xboole_0(sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | spl7_27 ),
    inference(subsumption_resolution,[],[f337,f98])).

fof(f337,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | v1_xboole_0(sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | spl7_27 ),
    inference(subsumption_resolution,[],[f336,f79])).

fof(f336,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | v1_xboole_0(sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_27 ),
    inference(subsumption_resolution,[],[f335,f69])).

fof(f335,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | v1_xboole_0(sK1)
    | ~ spl7_1
    | spl7_27 ),
    inference(resolution,[],[f333,f92])).

fof(f92,plain,
    ( ! [X21,X22,X20] :
        ( v1_funct_2(k5_funct_2(X22,X20,X21,sK3),X22,X21)
        | v1_xboole_0(X21)
        | v1_xboole_0(X22)
        | ~ v1_funct_2(sK3,X22,k2_zfmisc_1(X20,X21))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,k2_zfmisc_1(X20,X21))))
        | v1_xboole_0(X20) )
    | ~ spl7_1 ),
    inference(resolution,[],[f64,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
        & v1_funct_1(k5_funct_2(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_funct_2)).

fof(f333,plain,
    ( ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
    | spl7_27 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl7_27
  <=> v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f334,plain,
    ( spl7_26
    | ~ spl7_27
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f326,f210,f163,f101,f96,f77,f72,f67,f62,f331,f328])).

fof(f163,plain,
    ( spl7_12
  <=> v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f210,plain,
    ( spl7_14
  <=> m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f326,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(X0,sK0)
        | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f187,f212])).

fof(f212,plain,
    ( m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f210])).

fof(f187,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f186,f79])).

fof(f186,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f185,f103])).

% (2993)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f185,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f184,f98])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f183,f64])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) )
    | spl7_2
    | spl7_3
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f182,f69])).

fof(f182,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) )
    | spl7_3
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f172,f74])).

fof(f172,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1)
        | v1_xboole_0(sK2)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0)
        | ~ v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)
        | ~ m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ m1_subset_1(X0,sK0)
        | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0) )
    | ~ spl7_12 ),
    inference(resolution,[],[f165,f59])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(k5_funct_2(X0,X1,X2,X3))
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(X0)
      | ~ v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
      | ~ m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X5,X0)
      | k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) = k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X5,X0)
      | k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
      | k5_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                            | ~ m1_subset_1(X5,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                        & v1_funct_2(X4,X0,X2)
                        & v1_funct_1(X4) )
                     => ( k5_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,X0)
                           => k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_funct_2)).

fof(f165,plain,
    ( v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f289,plain,
    ( ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | spl7_22 ),
    inference(subsumption_resolution,[],[f287,f74])).

fof(f287,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | spl7_22 ),
    inference(subsumption_resolution,[],[f286,f103])).

fof(f286,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | v1_xboole_0(sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | spl7_22 ),
    inference(subsumption_resolution,[],[f285,f98])).

fof(f285,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | v1_xboole_0(sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | spl7_22 ),
    inference(subsumption_resolution,[],[f284,f79])).

fof(f284,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | v1_xboole_0(sK1)
    | ~ spl7_1
    | spl7_2
    | spl7_22 ),
    inference(subsumption_resolution,[],[f283,f69])).

fof(f283,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | v1_xboole_0(sK1)
    | ~ spl7_1
    | spl7_22 ),
    inference(resolution,[],[f278,f89])).

fof(f89,plain,
    ( ! [X12,X13,X11] :
        ( v1_funct_2(k4_funct_2(X13,X11,X12,sK3),X13,X11)
        | v1_xboole_0(X12)
        | v1_xboole_0(X13)
        | ~ v1_funct_2(sK3,X13,k2_zfmisc_1(X11,X12))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,k2_zfmisc_1(X11,X12))))
        | v1_xboole_0(X11) )
    | ~ spl7_1 ),
    inference(resolution,[],[f64,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
        & v1_funct_1(X3)
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
        & v1_funct_1(k4_funct_2(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_funct_2)).

fof(f278,plain,
    ( ~ v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f276])).

fof(f274,plain,
    ( spl7_21
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f262,f253,f108,f271])).

fof(f271,plain,
    ( spl7_21
  <=> k1_funct_1(sK3,sK4) = k4_tarski(k1_mcart_1(k1_funct_1(sK3,sK4)),k2_mcart_1(k1_funct_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f108,plain,
    ( spl7_8
  <=> v1_relat_1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f253,plain,
    ( spl7_20
  <=> r2_hidden(k1_funct_1(sK3,sK4),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f262,plain,
    ( k1_funct_1(sK3,sK4) = k4_tarski(k1_mcart_1(k1_funct_1(sK3,sK4)),k2_mcart_1(k1_funct_1(sK3,sK4)))
    | ~ spl7_8
    | ~ spl7_20 ),
    inference(resolution,[],[f255,f117])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 )
    | ~ spl7_8 ),
    inference(resolution,[],[f110,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f110,plain,
    ( v1_relat_1(k2_relat_1(sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f255,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),k2_relat_1(sK3))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f253])).

fof(f256,plain,
    ( spl7_20
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f244,f238,f226,f82,f253])).

fof(f226,plain,
    ( spl7_17
  <=> ! [X0] :
        ( r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3))
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f244,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),k2_relat_1(sK3))
    | ~ spl7_5
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f242,f84])).

fof(f242,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),k2_relat_1(sK3))
    | ~ m1_subset_1(sK4,sK0)
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(superposition,[],[f227,f240])).

fof(f227,plain,
    ( ! [X0] :
        ( r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f226])).

fof(f241,plain,
    ( spl7_19
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f215,f101,f96,f82,f77,f62,f238])).

fof(f215,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k1_funct_1(sK3,sK4)
    | ~ spl7_1
    | spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f130,f84])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl7_1
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f129,f79])).

fof(f129,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f128,f98])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0)
        | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0) = k1_funct_1(sK3,X0) )
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(resolution,[],[f94,f103])).

fof(f94,plain,
    ( ! [X28,X26,X27] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X26,X27)))
        | ~ v1_funct_2(sK3,X26,X27)
        | v1_xboole_0(X26)
        | ~ m1_subset_1(X28,X26)
        | k3_funct_2(X26,X27,sK3,X28) = k1_funct_1(sK3,X28) )
    | ~ spl7_1 ),
    inference(resolution,[],[f64,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f228,plain,
    ( spl7_16
    | spl7_17
    | ~ spl7_1
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f127,f119,f101,f96,f77,f62,f226,f222])).

fof(f119,plain,
    ( spl7_10
  <=> k2_relat_1(sK3) = k2_relset_1(sK0,k2_zfmisc_1(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f127,plain,
    ( ! [X0] :
        ( r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3))
        | v1_xboole_0(k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl7_1
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f126,f79])).

fof(f126,plain,
    ( ! [X0] :
        ( r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3))
        | v1_xboole_0(k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK0) )
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f125,f103])).

fof(f125,plain,
    ( ! [X0] :
        ( r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3))
        | v1_xboole_0(k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(X0,sK0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0) )
    | ~ spl7_1
    | ~ spl7_6
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f124,f98])).

fof(f124,plain,
    ( ! [X0] :
        ( r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3))
        | v1_xboole_0(k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(X0,sK0)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0) )
    | ~ spl7_1
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f123,f64])).

fof(f123,plain,
    ( ! [X0] :
        ( r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3))
        | v1_xboole_0(k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(X0,sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        | v1_xboole_0(sK0) )
    | ~ spl7_10 ),
    inference(superposition,[],[f47,f121])).

fof(f121,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK0,k2_zfmisc_1(sK1,sK2),sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).

fof(f213,plain,
    ( spl7_14
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f192,f101,f96,f77,f72,f67,f62,f210])).

fof(f192,plain,
    ( m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f191,f74])).

fof(f191,plain,
    ( v1_xboole_0(sK1)
    | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f190,f98])).

fof(f190,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f189,f79])).

fof(f189,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_1
    | spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f188,f69])).

fof(f188,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(resolution,[],[f93,f103])).

fof(f93,plain,
    ( ! [X24,X23,X25] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,k2_zfmisc_1(X23,X24))))
        | v1_xboole_0(X24)
        | v1_xboole_0(X25)
        | ~ v1_funct_2(sK3,X25,k2_zfmisc_1(X23,X24))
        | v1_xboole_0(X23)
        | m1_subset_1(k5_funct_2(X25,X23,X24,sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X24))) )
    | ~ spl7_1 ),
    inference(resolution,[],[f64,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f197,plain,
    ( spl7_13
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f171,f101,f96,f77,f72,f67,f62,f194])).

fof(f171,plain,
    ( m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f170,f74])).

fof(f170,plain,
    ( v1_xboole_0(sK1)
    | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f169,f98])).

fof(f169,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f168,f79])).

fof(f168,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_1
    | spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f167,f69])).

fof(f167,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(resolution,[],[f90,f103])).

fof(f90,plain,
    ( ! [X14,X15,X16] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X16,k2_zfmisc_1(X14,X15))))
        | v1_xboole_0(X15)
        | v1_xboole_0(X16)
        | ~ v1_funct_2(sK3,X16,k2_zfmisc_1(X14,X15))
        | v1_xboole_0(X14)
        | m1_subset_1(k4_funct_2(X16,X14,X15,sK3),k1_zfmisc_1(k2_zfmisc_1(X16,X14))) )
    | ~ spl7_1 ),
    inference(resolution,[],[f64,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f166,plain,
    ( spl7_12
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f145,f101,f96,f77,f72,f67,f62,f163])).

fof(f145,plain,
    ( v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f144,f74])).

fof(f144,plain,
    ( v1_xboole_0(sK1)
    | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f143,f98])).

fof(f143,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f142,f79])).

fof(f142,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f141,f69])).

fof(f141,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(resolution,[],[f91,f103])).

fof(f91,plain,
    ( ! [X19,X17,X18] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,k2_zfmisc_1(X17,X18))))
        | v1_xboole_0(X18)
        | v1_xboole_0(X19)
        | ~ v1_funct_2(sK3,X19,k2_zfmisc_1(X17,X18))
        | v1_xboole_0(X17)
        | v1_funct_1(k5_funct_2(X19,X17,X18,sK3)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f64,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_funct_1(k5_funct_2(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f140,plain,
    ( spl7_11
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f135,f101,f96,f77,f72,f67,f62,f137])).

fof(f135,plain,
    ( v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | spl7_2
    | spl7_3
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f134,f74])).

fof(f134,plain,
    ( v1_xboole_0(sK1)
    | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f133,f98])).

fof(f133,plain,
    ( ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | spl7_2
    | spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f132,f79])).

fof(f132,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | spl7_2
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f131,f69])).

fof(f131,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | v1_xboole_0(sK1)
    | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(resolution,[],[f88,f103])).

fof(f88,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,k2_zfmisc_1(X8,X9))))
        | v1_xboole_0(X9)
        | v1_xboole_0(X10)
        | ~ v1_funct_2(sK3,X10,k2_zfmisc_1(X8,X9))
        | v1_xboole_0(X8)
        | v1_funct_1(k4_funct_2(X10,X8,X9,sK3)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f64,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_funct_1(k4_funct_2(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f122,plain,
    ( spl7_10
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f106,f101,f119])).

fof(f106,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK0,k2_zfmisc_1(sK1,sK2),sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f103,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f116,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f34,f113])).

fof(f113,plain,
    ( spl7_9
  <=> k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f34,plain,(
    k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4))
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                      & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) = k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                    & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) = k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_funct_2)).

% (2994)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f111,plain,
    ( spl7_8
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f105,f101,f108])).

fof(f105,plain,
    ( v1_relat_1(k2_relat_1(sK3))
    | ~ spl7_7 ),
    inference(resolution,[],[f103,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_relat_1(k2_relat_1(X3)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(k2_relat_1(X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
     => v1_relat_1(k2_relat_1(X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relset_1)).

fof(f104,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f37,f101])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f99,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f36,f96])).

fof(f36,plain,(
    v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f33,f82])).

fof(f33,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f75,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f39,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f70,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:46:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (2995)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (3001)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (2992)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (2991)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (3002)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (3004)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (2991)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (3006)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (2996)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f389,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f99,f104,f111,f116,f122,f140,f166,f197,f213,f228,f241,f256,f274,f289,f334,f341,f352,f373,f374,f388])).
% 0.21/0.50  fof(f388,plain,(
% 0.21/0.50    spl7_2 | spl7_3 | ~spl7_16),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f387])).
% 0.21/0.50  fof(f387,plain,(
% 0.21/0.50    $false | (spl7_2 | spl7_3 | ~spl7_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f386,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1) | spl7_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl7_3 <=> v1_xboole_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | (spl7_2 | ~spl7_16)),
% 0.21/0.50    inference(subsumption_resolution,[],[f385,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ~v1_xboole_0(sK2) | spl7_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl7_2 <=> v1_xboole_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | v1_xboole_0(sK1) | ~spl7_16),
% 0.21/0.50    inference(resolution,[],[f224,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  % (2989)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | ~spl7_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f222])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    spl7_16 <=> v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4) != k1_mcart_1(k1_funct_1(sK3,sK4)) | k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) != k2_mcart_1(k1_funct_1(sK3,sK4)) | k1_funct_1(sK3,sK4) != k4_tarski(k1_mcart_1(k1_funct_1(sK3,sK4)),k2_mcart_1(k1_funct_1(sK3,sK4))) | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k1_funct_1(sK3,sK4) | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f373,plain,(
% 0.21/0.50    spl7_30 | ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_11 | ~spl7_13 | ~spl7_19 | ~spl7_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f325,f276,f238,f194,f137,f101,f96,f82,f77,f72,f67,f62,f370])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    spl7_30 <=> k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4) = k1_mcart_1(k1_funct_1(sK3,sK4))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl7_1 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl7_4 <=> v1_xboole_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl7_5 <=> m1_subset_1(sK4,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    spl7_6 <=> v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl7_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl7_11 <=> v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    spl7_13 <=> m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    spl7_19 <=> k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k1_funct_1(sK3,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    spl7_22 <=> v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.50  fof(f325,plain,(
% 0.21/0.50    k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4) = k1_mcart_1(k1_funct_1(sK3,sK4)) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_11 | ~spl7_13 | ~spl7_19 | ~spl7_22)),
% 0.21/0.50    inference(forward_demodulation,[],[f322,f240])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k1_funct_1(sK3,sK4) | ~spl7_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f238])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4) = k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_11 | ~spl7_13 | ~spl7_22)),
% 0.21/0.50    inference(resolution,[],[f321,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    m1_subset_1(sK4,sK0) | ~spl7_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,sK0) | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7 | ~spl7_11 | ~spl7_13 | ~spl7_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f320,f196])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f194])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7 | ~spl7_11 | ~spl7_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f161,f277])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) | ~spl7_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f276])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) | ~m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7 | ~spl7_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f160,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~v1_xboole_0(sK0) | spl7_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(sK0) | ~v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) | ~m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | ~spl7_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0) | ~v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) | ~m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_6 | ~spl7_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f158,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~spl7_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f96])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0) | ~v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) | ~m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl7_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  % (2990)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0) | ~v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) | ~m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (spl7_2 | spl7_3 | ~spl7_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f156,f69])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(sK2) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0) | ~v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) | ~m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (spl7_3 | ~spl7_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f146,f74])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0) | ~v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) | ~m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~m1_subset_1(X0,sK0) | k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X0)) ) | ~spl7_11),
% 0.21/0.50    inference(resolution,[],[f139,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(k4_funct_2(X0,X1,X2,X3)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | v1_xboole_0(X0) | ~v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1) | ~m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,X0) | k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) = k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X5)) )),
% 0.21/0.50    inference(equality_resolution,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,X0) | k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) | k4_funct_2(X0,X1,X2,X3) != X4) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k4_funct_2(X0,X1,X2,X3) = X4 <=> ! [X5] : (k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) | ~m1_subset_1(X5,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~v1_funct_1(X3)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k4_funct_2(X0,X1,X2,X3) = X4 <=> ! [X5] : (k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) | ~m1_subset_1(X5,X0))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~v1_funct_1(X3))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => (k4_funct_2(X0,X1,X2,X3) = X4 <=> ! [X5] : (m1_subset_1(X5,X0) => k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_funct_2)).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3)) | ~spl7_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f352,plain,(
% 0.21/0.50    spl7_28 | ~spl7_5 | ~spl7_19 | ~spl7_26),
% 0.21/0.50    inference(avatar_split_clause,[],[f345,f328,f238,f82,f349])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    spl7_28 <=> k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) = k2_mcart_1(k1_funct_1(sK3,sK4))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.50  fof(f328,plain,(
% 0.21/0.50    spl7_26 <=> ! [X0] : (~m1_subset_1(X0,sK0) | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.21/0.50  fof(f345,plain,(
% 0.21/0.50    k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) = k2_mcart_1(k1_funct_1(sK3,sK4)) | (~spl7_5 | ~spl7_19 | ~spl7_26)),
% 0.21/0.50    inference(forward_demodulation,[],[f342,f240])).
% 0.21/0.50  fof(f342,plain,(
% 0.21/0.50    k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4) = k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)) | (~spl7_5 | ~spl7_26)),
% 0.21/0.50    inference(resolution,[],[f329,f84])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,sK0) | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)) ) | ~spl7_26),
% 0.21/0.50    inference(avatar_component_clause,[],[f328])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7 | spl7_27),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f340])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    $false | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7 | spl7_27)),
% 0.21/0.50    inference(subsumption_resolution,[],[f339,f74])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_6 | ~spl7_7 | spl7_27)),
% 0.21/0.50    inference(subsumption_resolution,[],[f338,f103])).
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK1) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_6 | spl7_27)),
% 0.21/0.50    inference(subsumption_resolution,[],[f337,f98])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK1) | (~spl7_1 | spl7_2 | spl7_4 | spl7_27)),
% 0.21/0.50    inference(subsumption_resolution,[],[f336,f79])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK1) | (~spl7_1 | spl7_2 | spl7_27)),
% 0.21/0.50    inference(subsumption_resolution,[],[f335,f69])).
% 0.21/0.50  fof(f335,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK1) | (~spl7_1 | spl7_27)),
% 0.21/0.50    inference(resolution,[],[f333,f92])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X21,X22,X20] : (v1_funct_2(k5_funct_2(X22,X20,X21,sK3),X22,X21) | v1_xboole_0(X21) | v1_xboole_0(X22) | ~v1_funct_2(sK3,X22,k2_zfmisc_1(X20,X21)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X22,k2_zfmisc_1(X20,X21)))) | v1_xboole_0(X20)) ) | ~spl7_1),
% 0.21/0.50    inference(resolution,[],[f64,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2) & v1_funct_1(k5_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~v1_funct_1(X3) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2) & v1_funct_1(k5_funct_2(X0,X1,X2,X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~v1_funct_1(X3) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) & v1_funct_1(X3) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2) & v1_funct_1(k5_funct_2(X0,X1,X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_funct_2)).
% 0.21/0.50  fof(f333,plain,(
% 0.21/0.50    ~v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) | spl7_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f331])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    spl7_27 <=> v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    spl7_26 | ~spl7_27 | ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7 | ~spl7_12 | ~spl7_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f326,f210,f163,f101,f96,f77,f72,f67,f62,f331,f328])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    spl7_12 <=> v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.50  fof(f210,plain,(
% 0.21/0.50    spl7_14 <=> m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.50  fof(f326,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) | ~m1_subset_1(X0,sK0) | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7 | ~spl7_12 | ~spl7_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f187,f212])).
% 0.21/0.50  fof(f212,plain,(
% 0.21/0.50    m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl7_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f210])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) | ~m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X0,sK0) | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7 | ~spl7_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f186,f79])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(sK0) | ~v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) | ~m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X0,sK0) | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_6 | ~spl7_7 | ~spl7_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f185,f103])).
% 0.21/0.50  % (2993)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0) | ~v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) | ~m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X0,sK0) | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_6 | ~spl7_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f98])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0) | ~v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) | ~m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X0,sK0) | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (~spl7_1 | spl7_2 | spl7_3 | ~spl7_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f183,f64])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0) | ~v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) | ~m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X0,sK0) | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (spl7_2 | spl7_3 | ~spl7_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f182,f69])).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(sK2) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0) | ~v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) | ~m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X0,sK0) | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)) ) | (spl7_3 | ~spl7_12)),
% 0.21/0.50    inference(subsumption_resolution,[],[f172,f74])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0) | ~v1_funct_2(k5_funct_2(sK0,sK1,sK2,sK3),sK0,sK2) | ~m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~m1_subset_1(X0,sK0) | k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)) ) | ~spl7_12),
% 0.21/0.50    inference(resolution,[],[f165,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_1(k5_funct_2(X0,X1,X2,X3)) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | v1_xboole_0(X0) | ~v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2) | ~m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X5,X0) | k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) = k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X5)) )),
% 0.21/0.50    inference(equality_resolution,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(X5,X0) | k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) | k5_funct_2(X0,X1,X2,X3) != X4) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k5_funct_2(X0,X1,X2,X3) = X4 <=> ! [X5] : (k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) | ~m1_subset_1(X5,X0))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X4,X0,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~v1_funct_1(X3)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k5_funct_2(X0,X1,X2,X3) = X4 <=> ! [X5] : (k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)) | ~m1_subset_1(X5,X0))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X4,X0,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~v1_funct_1(X3))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X4,X0,X2) & v1_funct_1(X4)) => (k5_funct_2(X0,X1,X2,X3) = X4 <=> ! [X5] : (m1_subset_1(X5,X0) => k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5)))))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_funct_2)).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3)) | ~spl7_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f163])).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7 | spl7_22),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f288])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    $false | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7 | spl7_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f287,f74])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_6 | ~spl7_7 | spl7_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f286,f103])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK1) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_6 | spl7_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f285,f98])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK1) | (~spl7_1 | spl7_2 | spl7_4 | spl7_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f284,f79])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK1) | (~spl7_1 | spl7_2 | spl7_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f283,f69])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK1) | (~spl7_1 | spl7_22)),
% 0.21/0.50    inference(resolution,[],[f278,f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X12,X13,X11] : (v1_funct_2(k4_funct_2(X13,X11,X12,sK3),X13,X11) | v1_xboole_0(X12) | v1_xboole_0(X13) | ~v1_funct_2(sK3,X13,k2_zfmisc_1(X11,X12)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X13,k2_zfmisc_1(X11,X12)))) | v1_xboole_0(X11)) ) | ~spl7_1),
% 0.21/0.50    inference(resolution,[],[f64,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1) & v1_funct_1(k4_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~v1_funct_1(X3) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1) & v1_funct_1(k4_funct_2(X0,X1,X2,X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~v1_funct_1(X3) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) & v1_funct_1(X3) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1) & v1_funct_1(k4_funct_2(X0,X1,X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_funct_2)).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    ~v1_funct_2(k4_funct_2(sK0,sK1,sK2,sK3),sK0,sK1) | spl7_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f276])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    spl7_21 | ~spl7_8 | ~spl7_20),
% 0.21/0.50    inference(avatar_split_clause,[],[f262,f253,f108,f271])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    spl7_21 <=> k1_funct_1(sK3,sK4) = k4_tarski(k1_mcart_1(k1_funct_1(sK3,sK4)),k2_mcart_1(k1_funct_1(sK3,sK4)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl7_8 <=> v1_relat_1(k2_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    spl7_20 <=> r2_hidden(k1_funct_1(sK3,sK4),k2_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    k1_funct_1(sK3,sK4) = k4_tarski(k1_mcart_1(k1_funct_1(sK3,sK4)),k2_mcart_1(k1_funct_1(sK3,sK4))) | (~spl7_8 | ~spl7_20)),
% 0.21/0.50    inference(resolution,[],[f255,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) ) | ~spl7_8),
% 0.21/0.50    inference(resolution,[],[f110,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    v1_relat_1(k2_relat_1(sK3)) | ~spl7_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f108])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    r2_hidden(k1_funct_1(sK3,sK4),k2_relat_1(sK3)) | ~spl7_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f253])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    spl7_20 | ~spl7_5 | ~spl7_17 | ~spl7_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f244,f238,f226,f82,f253])).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    spl7_17 <=> ! [X0] : (r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3)) | ~m1_subset_1(X0,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    r2_hidden(k1_funct_1(sK3,sK4),k2_relat_1(sK3)) | (~spl7_5 | ~spl7_17 | ~spl7_19)),
% 0.21/0.50    inference(subsumption_resolution,[],[f242,f84])).
% 0.21/0.50  fof(f242,plain,(
% 0.21/0.50    r2_hidden(k1_funct_1(sK3,sK4),k2_relat_1(sK3)) | ~m1_subset_1(sK4,sK0) | (~spl7_17 | ~spl7_19)),
% 0.21/0.50    inference(superposition,[],[f227,f240])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3)) | ~m1_subset_1(X0,sK0)) ) | ~spl7_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f226])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    spl7_19 | ~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f215,f101,f96,f82,f77,f62,f238])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k1_funct_1(sK3,sK4) | (~spl7_1 | spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(resolution,[],[f130,f84])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl7_1 | spl7_4 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f129,f79])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl7_1 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f128,f98])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK0) | ~m1_subset_1(X0,sK0) | k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0) = k1_funct_1(sK3,X0)) ) | (~spl7_1 | ~spl7_7)),
% 0.21/0.50    inference(resolution,[],[f94,f103])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X28,X26,X27] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X26,X27))) | ~v1_funct_2(sK3,X26,X27) | v1_xboole_0(X26) | ~m1_subset_1(X28,X26) | k3_funct_2(X26,X27,sK3,X28) = k1_funct_1(sK3,X28)) ) | ~spl7_1),
% 0.21/0.50    inference(resolution,[],[f64,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    spl7_16 | spl7_17 | ~spl7_1 | spl7_4 | ~spl7_6 | ~spl7_7 | ~spl7_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f127,f119,f101,f96,f77,f62,f226,f222])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl7_10 <=> k2_relat_1(sK3) = k2_relset_1(sK0,k2_zfmisc_1(sK1,sK2),sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3)) | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(X0,sK0)) ) | (~spl7_1 | spl7_4 | ~spl7_6 | ~spl7_7 | ~spl7_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f126,f79])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3)) | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0)) ) | (~spl7_1 | ~spl7_6 | ~spl7_7 | ~spl7_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f125,f103])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3)) | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0)) ) | (~spl7_1 | ~spl7_6 | ~spl7_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f124,f98])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3)) | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(X0,sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0)) ) | (~spl7_1 | ~spl7_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f123,f64])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0),k2_relat_1(sK3)) | v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(X0,sK0) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) | v1_xboole_0(sK0)) ) | ~spl7_10),
% 0.21/0.50    inference(superposition,[],[f47,f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    k2_relat_1(sK3) = k2_relset_1(sK0,k2_zfmisc_1(sK1,sK2),sK3) | ~spl7_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | v1_xboole_0(X1) | ~m1_subset_1(X2,X0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).
% 0.21/0.50  fof(f213,plain,(
% 0.21/0.50    spl7_14 | ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f192,f101,f96,f77,f72,f67,f62,f210])).
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f191,f74])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f190,f98])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f189,f79])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl7_1 | spl7_2 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f69])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | m1_subset_1(k5_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl7_1 | ~spl7_7)),
% 0.21/0.50    inference(resolution,[],[f93,f103])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X24,X23,X25] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X25,k2_zfmisc_1(X23,X24)))) | v1_xboole_0(X24) | v1_xboole_0(X25) | ~v1_funct_2(sK3,X25,k2_zfmisc_1(X23,X24)) | v1_xboole_0(X23) | m1_subset_1(k5_funct_2(X25,X23,X24,sK3),k1_zfmisc_1(k2_zfmisc_1(X25,X24)))) ) | ~spl7_1),
% 0.21/0.50    inference(resolution,[],[f64,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    spl7_13 | ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f171,f101,f96,f77,f72,f67,f62,f194])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f170,f74])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f169,f98])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f168,f79])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl7_1 | spl7_2 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f167,f69])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | m1_subset_1(k4_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl7_1 | ~spl7_7)),
% 0.21/0.50    inference(resolution,[],[f90,f103])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X14,X15,X16] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X16,k2_zfmisc_1(X14,X15)))) | v1_xboole_0(X15) | v1_xboole_0(X16) | ~v1_funct_2(sK3,X16,k2_zfmisc_1(X14,X15)) | v1_xboole_0(X14) | m1_subset_1(k4_funct_2(X16,X14,X15,sK3),k1_zfmisc_1(k2_zfmisc_1(X16,X14)))) ) | ~spl7_1),
% 0.21/0.50    inference(resolution,[],[f64,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    spl7_12 | ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f145,f101,f96,f77,f72,f67,f62,f163])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3)) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f144,f74])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3)) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f143,f98])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3)) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f142,f79])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3)) | (~spl7_1 | spl7_2 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f141,f69])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | v1_funct_1(k5_funct_2(sK0,sK1,sK2,sK3)) | (~spl7_1 | ~spl7_7)),
% 0.21/0.50    inference(resolution,[],[f91,f103])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X19,X17,X18] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X19,k2_zfmisc_1(X17,X18)))) | v1_xboole_0(X18) | v1_xboole_0(X19) | ~v1_funct_2(sK3,X19,k2_zfmisc_1(X17,X18)) | v1_xboole_0(X17) | v1_funct_1(k5_funct_2(X19,X17,X18,sK3))) ) | ~spl7_1),
% 0.21/0.50    inference(resolution,[],[f64,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | v1_funct_1(k5_funct_2(X0,X1,X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl7_11 | ~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f135,f101,f96,f77,f72,f67,f62,f137])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3)) | (~spl7_1 | spl7_2 | spl7_3 | spl7_4 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f134,f74])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    v1_xboole_0(sK1) | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3)) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_6 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f133,f98])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3)) | (~spl7_1 | spl7_2 | spl7_4 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f132,f79])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3)) | (~spl7_1 | spl7_2 | ~spl7_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f131,f69])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) | v1_xboole_0(sK1) | v1_funct_1(k4_funct_2(sK0,sK1,sK2,sK3)) | (~spl7_1 | ~spl7_7)),
% 0.21/0.50    inference(resolution,[],[f88,f103])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X10,X8,X9] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X10,k2_zfmisc_1(X8,X9)))) | v1_xboole_0(X9) | v1_xboole_0(X10) | ~v1_funct_2(sK3,X10,k2_zfmisc_1(X8,X9)) | v1_xboole_0(X8) | v1_funct_1(k4_funct_2(X10,X8,X9,sK3))) ) | ~spl7_1),
% 0.21/0.50    inference(resolution,[],[f64,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | v1_xboole_0(X1) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | v1_funct_1(k4_funct_2(X0,X1,X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl7_10 | ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f106,f101,f119])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    k2_relat_1(sK3) = k2_relset_1(sK0,k2_zfmisc_1(sK1,sK2),sK3) | ~spl7_7),
% 0.21/0.50    inference(resolution,[],[f103,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ~spl7_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    spl7_9 <=> k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)) & m1_subset_1(X4,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,X0) => k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) = k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f11])).
% 0.21/0.50  fof(f11,conjecture,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) & v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2)) & v1_funct_1(X3)) => ! [X4] : (m1_subset_1(X4,X0) => k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X4) = k4_tarski(k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X4),k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X4)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t196_funct_2)).
% 0.21/0.50  % (2994)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl7_8 | ~spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f105,f101,f108])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    v1_relat_1(k2_relat_1(sK3)) | ~spl7_7),
% 0.21/0.50    inference(resolution,[],[f103,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) | v1_relat_1(k2_relat_1(X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (v1_relat_1(k2_relat_1(X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) => v1_relat_1(k2_relat_1(X3)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relset_1)).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl7_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f101])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl7_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f96])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl7_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f82])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    m1_subset_1(sK4,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ~spl7_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f77])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ~v1_xboole_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~spl7_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f72])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ~v1_xboole_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~spl7_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f67])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ~v1_xboole_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl7_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f62])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (2991)------------------------------
% 0.21/0.50  % (2991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2991)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (2991)Memory used [KB]: 10874
% 0.21/0.50  % (2991)Time elapsed: 0.082 s
% 0.21/0.50  % (2991)------------------------------
% 0.21/0.50  % (2991)------------------------------
% 0.21/0.51  % (2987)Success in time 0.149 s
%------------------------------------------------------------------------------
