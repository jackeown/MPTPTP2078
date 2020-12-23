%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1128+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:08 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 130 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  158 ( 403 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2351,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2350,f2053])).

fof(f2053,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f1956,f2010])).

fof(f2010,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f1942,f1900])).

fof(f1900,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1859])).

fof(f1859,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1777])).

fof(f1777,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f1942,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f1890,f1920])).

fof(f1920,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1871])).

fof(f1871,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f1890,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f1877])).

fof(f1877,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f1852,f1876,f1875])).

fof(f1875,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m1_pre_topc(X1,X0)
            & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m1_pre_topc(X1,sK2)
          & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1876,plain,
    ( ? [X1] :
        ( ~ m1_pre_topc(X1,sK2)
        & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
   => ( ~ m1_pre_topc(sK3,sK2)
      & m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f1852,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m1_pre_topc(X1,X0)
          & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1848])).

fof(f1848,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
           => m1_pre_topc(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f1847])).

fof(f1847,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f1956,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f1891,f1896])).

fof(f1896,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1857])).

fof(f1857,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f1891,plain,(
    m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f1877])).

fof(f2350,plain,(
    ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f2347,f1892])).

fof(f1892,plain,(
    ~ m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f1877])).

fof(f2347,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f2194,f1931])).

fof(f1931,plain,(
    ! [X0] : sQ9_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f1923])).

fof(f1923,plain,(
    ! [X1,X0] :
      ( sQ9_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ9_eqProxy])])).

fof(f2194,plain,(
    ! [X0] :
      ( ~ sQ9_eqProxy(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f2193,f2009])).

fof(f2009,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f1942,f1899])).

fof(f1899,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1859])).

fof(f2193,plain,(
    ! [X0] :
      ( ~ sQ9_eqProxy(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0)
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    inference(subsumption_resolution,[],[f2192,f2010])).

fof(f2192,plain,(
    ! [X0] :
      ( ~ sQ9_eqProxy(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    inference(subsumption_resolution,[],[f2191,f1890])).

fof(f2191,plain,(
    ! [X0] :
      ( ~ sQ9_eqProxy(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    inference(subsumption_resolution,[],[f2190,f2053])).

fof(f2190,plain,(
    ! [X0] :
      ( ~ sQ9_eqProxy(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    inference(duplicate_literal_removal,[],[f2185])).

fof(f2185,plain,(
    ! [X0] :
      ( ~ sQ9_eqProxy(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    inference(resolution,[],[f1955,f1927])).

fof(f1927,plain,(
    ! [X0] :
      ( sQ9_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0)
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f1905,f1923])).

fof(f1905,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1867])).

fof(f1867,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1866])).

fof(f1866,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f1955,plain,(
    ! [X0,X1] :
      ( ~ sQ9_eqProxy(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ sQ9_eqProxy(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(sK3)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ) ),
    inference(resolution,[],[f1891,f1926])).

fof(f1926,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ sQ9_eqProxy(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
      | ~ sQ9_eqProxy(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_proxy_replacement,[],[f1903,f1923,f1923])).

fof(f1903,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1863])).

fof(f1863,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1862])).

fof(f1862,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(X3,X1)
                  | ~ m1_pre_topc(X2,X0)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ l1_pre_topc(X3) )
              | ~ l1_pre_topc(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1828])).

fof(f1828,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( l1_pre_topc(X2)
             => ! [X3] :
                  ( l1_pre_topc(X3)
                 => ( ( m1_pre_topc(X2,X0)
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_pre_topc)).
%------------------------------------------------------------------------------
