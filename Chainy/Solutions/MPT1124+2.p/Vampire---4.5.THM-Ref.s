%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1124+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:08 EST 2020

% Result     : Theorem 1.09s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 122 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  185 ( 523 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2474,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2061,f2098,f2106,f2470])).

fof(f2470,plain,
    ( ~ spl17_8
    | ~ spl17_13 ),
    inference(avatar_contradiction_clause,[],[f2469])).

fof(f2469,plain,
    ( $false
    | ~ spl17_8
    | ~ spl17_13 ),
    inference(subsumption_resolution,[],[f2468,f2444])).

fof(f2444,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_13 ),
    inference(resolution,[],[f2102,f2091])).

fof(f2091,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | ~ spl17_13 ),
    inference(avatar_component_clause,[],[f2089])).

fof(f2089,plain,
    ( spl17_13
  <=> r2_hidden(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_13])])).

fof(f2102,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f1938,f1951])).

fof(f1951,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1861])).

fof(f1861,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f1860])).

fof(f1860,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f1938,plain,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f1897])).

fof(f1897,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f1844,f1896,f1895,f1894])).

fof(f1894,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,u1_struct_0(X0))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(sK0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1895,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(X2,u1_struct_0(sK0))
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(sK0))
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1896,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f1844,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f1843])).

fof(f1843,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1840])).

fof(f1840,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1839])).

fof(f1839,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f2468,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_8 ),
    inference(forward_demodulation,[],[f2467,f2114])).

fof(f2114,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl17_8 ),
    inference(resolution,[],[f2050,f1999])).

fof(f1999,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1893])).

fof(f1893,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1771])).

fof(f1771,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f2050,plain,
    ( l1_struct_0(sK1)
    | ~ spl17_8 ),
    inference(avatar_component_clause,[],[f2049])).

fof(f2049,plain,
    ( spl17_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_8])])).

fof(f2467,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl17_8 ),
    inference(subsumption_resolution,[],[f2456,f2050])).

fof(f2456,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f2076,f1998])).

fof(f1998,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1892])).

fof(f1892,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1779])).

fof(f1779,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f2076,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2073,f1934])).

fof(f1934,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f1897])).

fof(f2073,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f1936,f1942])).

fof(f1942,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1848])).

fof(f1848,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1825])).

fof(f1825,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f1936,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f1897])).

fof(f2106,plain,(
    spl17_8 ),
    inference(avatar_contradiction_clause,[],[f2105])).

fof(f2105,plain,
    ( $false
    | spl17_8 ),
    inference(subsumption_resolution,[],[f2104,f2075])).

fof(f2075,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f2072,f1934])).

fof(f2072,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1936,f1943])).

fof(f1943,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1849])).

fof(f1849,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f2104,plain,
    ( ~ l1_pre_topc(sK1)
    | spl17_8 ),
    inference(resolution,[],[f2051,f1997])).

fof(f1997,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1891])).

fof(f1891,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1780])).

fof(f1780,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2051,plain,
    ( ~ l1_struct_0(sK1)
    | spl17_8 ),
    inference(avatar_component_clause,[],[f2049])).

fof(f2098,plain,
    ( spl17_10
    | spl17_13 ),
    inference(avatar_split_clause,[],[f2087,f2089,f2058])).

fof(f2058,plain,
    ( spl17_10
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).

fof(f2087,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f1937,f1970])).

fof(f1970,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1876])).

fof(f1876,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f1875])).

fof(f1875,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f1937,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f1897])).

fof(f2061,plain,
    ( ~ spl17_8
    | ~ spl17_10 ),
    inference(avatar_split_clause,[],[f2045,f2058,f2049])).

fof(f2045,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f1935,f1949])).

fof(f1949,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1857])).

fof(f1857,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f1856])).

fof(f1856,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1793])).

fof(f1793,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f1935,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f1897])).
%------------------------------------------------------------------------------
