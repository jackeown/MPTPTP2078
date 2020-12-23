%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1079+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 232 expanded)
%              Number of leaves         :   29 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  692 (1540 expanded)
%              Number of equality atoms :   87 ( 200 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f94,f98,f102,f122,f135,f143,f178,f180])).

fof(f180,plain,
    ( spl7_7
    | spl7_6
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f179,f176,f92,f96])).

fof(f96,plain,
    ( spl7_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f92,plain,
    ( spl7_6
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f176,plain,
    ( spl7_17
  <=> v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f179,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ spl7_17 ),
    inference(resolution,[],[f177,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

fof(f177,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( spl7_8
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | ~ spl7_2
    | spl7_17
    | spl7_11 ),
    inference(avatar_split_clause,[],[f174,f141,f176,f76,f80,f84,f88,f100])).

fof(f100,plain,
    ( spl7_8
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f88,plain,
    ( spl7_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f84,plain,
    ( spl7_4
  <=> v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f80,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f76,plain,
    ( spl7_2
  <=> m1_subset_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f141,plain,
    ( spl7_11
  <=> k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f174,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | ~ m1_subset_1(sK4,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | spl7_11 ),
    inference(resolution,[],[f173,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),k2_zfmisc_1(X0,X1))
        | v1_xboole_0(k2_zfmisc_1(X0,X1)) )
    | spl7_11 ),
    inference(resolution,[],[f172,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f172,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),X0) )
    | spl7_11 ),
    inference(resolution,[],[f168,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f168,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),X0)
        | ~ v1_relat_1(X0) )
    | spl7_11 ),
    inference(trivial_inequality_removal,[],[f167])).

fof(f167,plain,
    ( ! [X0] :
        ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)
        | ~ r2_hidden(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4),X0)
        | ~ v1_relat_1(X0) )
    | spl7_11 ),
    inference(superposition,[],[f142,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f142,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( ~ spl7_2
    | ~ spl7_11
    | spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f136,f133,f120,f141,f76])).

fof(f120,plain,
    ( spl7_9
  <=> k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f133,plain,
    ( spl7_10
  <=> ! [X0] :
        ( k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)
        | ~ m1_subset_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f136,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)))
    | ~ m1_subset_1(sK4,sK0)
    | spl7_9
    | ~ spl7_10 ),
    inference(superposition,[],[f121,f134])).

fof(f134,plain,
    ( ! [X0] :
        ( k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f121,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f135,plain,
    ( spl7_8
    | spl7_7
    | spl7_6
    | ~ spl7_4
    | spl7_10
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f131,f88,f80,f133,f84,f92,f96,f100])).

fof(f131,plain,
    ( ! [X0] :
        ( k2_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X0)) = k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X0)
        | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
        | ~ m1_subset_1(X0,sK0)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK1)
        | v1_xboole_0(sK0) )
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(resolution,[],[f128,f81])).

fof(f81,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f128,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
        | k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),sK3,X3)) = k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,sK3),X3)
        | ~ v1_funct_2(sK3,X0,k2_zfmisc_1(X1,X2))
        | ~ m1_subset_1(X3,X0)
        | v1_xboole_0(X2)
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f125,f89])).

fof(f89,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f125,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X4)
      | k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X0)) = k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
      | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,X1)
      | k2_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X0)) = k3_funct_2(X1,X3,k5_funct_2(X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
      | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
      | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f106,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k5_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_funct_2)).

fof(f106,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ v1_funct_1(k5_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X6,X0)
      | k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6)) = k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X6)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f105,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f105,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6)) = k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X6)
      | ~ m1_subset_1(X6,X0)
      | ~ v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
      | ~ v1_funct_1(k5_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f70,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6)) = k3_funct_2(X0,X2,k5_funct_2(X0,X1,X2,X3),X6)
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(k5_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(k5_funct_2(X0,X1,X2,X3),X0,X2)
      | ~ v1_funct_1(k5_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X2,X4,X6) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
      | ~ m1_subset_1(X6,X0)
      | k5_funct_2(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X4,X0,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k5_funct_2(X0,X1,X2,X3) = X4
                          | ( k3_funct_2(X0,X2,X4,sK6(X0,X1,X2,X3,X4)) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK6(X0,X1,X2,X3,X4)))
                            & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X2,X4,X6) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k5_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X2,X4,X5) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X2,X4,sK6(X0,X1,X2,X3,X4)) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK6(X0,X1,X2,X3,X4)))
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k5_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X2,X4,X5) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X2,X4,X6) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k5_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k5_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X2,X4,X5) != k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X5] :
                              ( k3_funct_2(X0,X2,X4,X5) = k2_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              | ~ m1_subset_1(X5,X0) )
                          | k5_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      | ~ v1_funct_2(X4,X0,X2)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_funct_2)).

fof(f122,plain,
    ( spl7_8
    | spl7_7
    | spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | ~ spl7_3
    | ~ spl7_2
    | ~ spl7_9
    | spl7_1 ),
    inference(avatar_split_clause,[],[f109,f72,f120,f76,f80,f84,f88,f92,f96,f100])).

fof(f72,plain,
    ( spl7_1
  <=> k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) = k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f109,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k1_mcart_1(k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4)),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | ~ m1_subset_1(sK4,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    | ~ v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl7_1 ),
    inference(superposition,[],[f73,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X0)) = k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
      | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,X1)
      | k1_mcart_1(k3_funct_2(X1,k2_zfmisc_1(X2,X3),X4,X0)) = k3_funct_2(X1,X2,k4_funct_2(X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
      | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X3))))
      | ~ v1_funct_2(X4,X1,k2_zfmisc_1(X2,X3))
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f104,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k4_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_funct_2)).

fof(f104,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ v1_funct_1(k4_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X6,X0)
      | k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6)) = k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X6)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f103,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f103,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6)) = k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X6)
      | ~ m1_subset_1(X6,X0)
      | ~ v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
      | ~ v1_funct_1(k4_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f69,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6)) = k3_funct_2(X0,X1,k4_funct_2(X0,X1,X2,X3),X6)
      | ~ m1_subset_1(X6,X0)
      | ~ m1_subset_1(k4_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(k4_funct_2(X0,X1,X2,X3),X0,X1)
      | ~ v1_funct_1(k4_funct_2(X0,X1,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X4,X6) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
      | ~ m1_subset_1(X6,X0)
      | k4_funct_2(X0,X1,X2,X3) != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k4_funct_2(X0,X1,X2,X3) = X4
                          | ( k3_funct_2(X0,X1,X4,sK5(X0,X1,X2,X3,X4)) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK5(X0,X1,X2,X3,X4)))
                            & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X1,X4,X6) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k4_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( k3_funct_2(X0,X1,X4,X5) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
          & m1_subset_1(X5,X0) )
     => ( k3_funct_2(X0,X1,X4,sK5(X0,X1,X2,X3,X4)) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,sK5(X0,X1,X2,X3,X4)))
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k4_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X1,X4,X5) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X6] :
                              ( k3_funct_2(X0,X1,X4,X6) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X6))
                              | ~ m1_subset_1(X6,X0) )
                          | k4_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( k4_funct_2(X0,X1,X2,X3) = X4
                          | ? [X5] :
                              ( k3_funct_2(X0,X1,X4,X5) != k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              & m1_subset_1(X5,X0) ) )
                        & ( ! [X5] :
                              ( k3_funct_2(X0,X1,X4,X5) = k1_mcart_1(k3_funct_2(X0,k2_zfmisc_1(X1,X2),X3,X5))
                              | ~ m1_subset_1(X5,X0) )
                          | k4_funct_2(X0,X1,X2,X3) != X4 ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_2(X4,X0,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
                  | ~ v1_funct_2(X3,X0,k2_zfmisc_1(X1,X2))
                  | ~ v1_funct_1(X3) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_funct_2)).

fof(f73,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f102,plain,(
    ~ spl7_8 ),
    inference(avatar_split_clause,[],[f44,f100])).

fof(f44,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
    & m1_subset_1(sK4,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
    & v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f34,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
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
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( k3_funct_2(sK0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(sK0,X1,k4_funct_2(sK0,X1,X2,X3),X4),k3_funct_2(sK0,X2,k5_funct_2(sK0,X1,X2,X3),X4))
                      & m1_subset_1(X4,sK0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(X1,X2))))
                  & v1_funct_2(X3,sK0,k2_zfmisc_1(X1,X2))
                  & v1_funct_1(X3) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( k3_funct_2(sK0,k2_zfmisc_1(X1,X2),X3,X4) != k4_tarski(k3_funct_2(sK0,X1,k4_funct_2(sK0,X1,X2,X3),X4),k3_funct_2(sK0,X2,k5_funct_2(sK0,X1,X2,X3),X4))
                    & m1_subset_1(X4,sK0) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(X1,X2))))
                & v1_funct_2(X3,sK0,k2_zfmisc_1(X1,X2))
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( k3_funct_2(sK0,k2_zfmisc_1(sK1,X2),X3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,X2,X3),X4),k3_funct_2(sK0,X2,k5_funct_2(sK0,sK1,X2,X3),X4))
                  & m1_subset_1(X4,sK0) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,X2))))
              & v1_funct_2(X3,sK0,k2_zfmisc_1(sK1,X2))
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( k3_funct_2(sK0,k2_zfmisc_1(sK1,X2),X3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,X2,X3),X4),k3_funct_2(sK0,X2,k5_funct_2(sK0,sK1,X2,X3),X4))
                & m1_subset_1(X4,sK0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,X2))))
            & v1_funct_2(X3,sK0,k2_zfmisc_1(sK1,X2))
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),X3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,X3),X4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,X3),X4))
              & m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
          & v1_funct_2(X3,sK0,k2_zfmisc_1(sK1,sK2))
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),X3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,X3),X4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,X3),X4))
            & m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
        & v1_funct_2(X3,sK0,k2_zfmisc_1(sK1,sK2))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X4))
          & m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2))))
      & v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X4] :
        ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,X4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),X4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),X4))
        & m1_subset_1(X4,sK0) )
   => ( k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4))
      & m1_subset_1(sK4,sK0) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_funct_2)).

fof(f98,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f45,f96])).

fof(f45,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f90,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f48,f84])).

fof(f48,plain,(
    v1_funct_2(sK3,sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f49,f80])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_zfmisc_1(sK1,sK2)))) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f50,f76])).

fof(f50,plain,(
    m1_subset_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f51,f72])).

fof(f51,plain,(
    k3_funct_2(sK0,k2_zfmisc_1(sK1,sK2),sK3,sK4) != k4_tarski(k3_funct_2(sK0,sK1,k4_funct_2(sK0,sK1,sK2,sK3),sK4),k3_funct_2(sK0,sK2,k5_funct_2(sK0,sK1,sK2,sK3),sK4)) ),
    inference(cnf_transformation,[],[f35])).

%------------------------------------------------------------------------------
