%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t30_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:09 EDT 2019

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 337 expanded)
%              Number of leaves         :   27 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  420 (1211 expanded)
%              Number of equality atoms :   52 ( 136 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3598,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f2131,f2256,f2355,f2357,f3433,f3437,f3597])).

fof(f3597,plain,
    ( spl8_1
    | ~ spl8_150 ),
    inference(avatar_contradiction_clause,[],[f3596])).

fof(f3596,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_150 ),
    inference(subsumption_resolution,[],[f3589,f531])).

fof(f531,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f529,f106])).

fof(f106,plain,
    ( ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_1
  <=> ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f529,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f91,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f51])).

fof(f51,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
        | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',t30_relset_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',redefinition_k1_relset_1)).

fof(f3589,plain,
    ( r1_tarski(sK2,k1_relat_1(sK3))
    | ~ spl8_1
    | ~ spl8_150 ),
    inference(resolution,[],[f3483,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f61,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',d3_tarski)).

fof(f3483,plain,
    ( r2_hidden(sK7(sK2,k1_relat_1(sK3)),k1_relat_1(sK3))
    | ~ spl8_1
    | ~ spl8_150 ),
    inference(resolution,[],[f532,f2255])).

fof(f2255,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl8_150 ),
    inference(avatar_component_clause,[],[f2254])).

fof(f2254,plain,
    ( spl8_150
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k1_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_150])])).

fof(f532,plain,
    ( r2_hidden(sK7(sK2,k1_relat_1(sK3)),sK2)
    | ~ spl8_1 ),
    inference(backward_demodulation,[],[f529,f372])).

fof(f372,plain,
    ( r2_hidden(sK7(sK2,k1_relset_1(sK0,sK1,sK3)),sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f106,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f3437,plain,(
    spl8_149 ),
    inference(avatar_contradiction_clause,[],[f3435])).

fof(f3435,plain,
    ( $false
    | ~ spl8_149 ),
    inference(resolution,[],[f3434,f65])).

fof(f3434,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl8_149 ),
    inference(resolution,[],[f2252,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',cc1_relset_1)).

fof(f2252,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl8_149 ),
    inference(avatar_component_clause,[],[f2251])).

fof(f2251,plain,
    ( spl8_149
  <=> ~ v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).

fof(f3433,plain,
    ( spl8_3
    | ~ spl8_144
    | ~ spl8_148 ),
    inference(avatar_contradiction_clause,[],[f3432])).

fof(f3432,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_144
    | ~ spl8_148 ),
    inference(subsumption_resolution,[],[f3426,f2435])).

fof(f2435,plain,
    ( ~ r1_tarski(sK2,k2_relat_1(sK3))
    | ~ spl8_3 ),
    inference(backward_demodulation,[],[f567,f112])).

fof(f112,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_3
  <=> ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f567,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f92,f65])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',redefinition_k2_relset_1)).

fof(f3426,plain,
    ( r1_tarski(sK2,k2_relat_1(sK3))
    | ~ spl8_3
    | ~ spl8_144
    | ~ spl8_148 ),
    inference(resolution,[],[f3001,f83])).

fof(f3001,plain,
    ( r2_hidden(sK7(sK2,k2_relat_1(sK3)),k2_relat_1(sK3))
    | ~ spl8_3
    | ~ spl8_144
    | ~ spl8_148 ),
    inference(resolution,[],[f2998,f2439])).

fof(f2439,plain,
    ( r2_hidden(sK7(sK2,k2_relat_1(sK3)),sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f2435,f82])).

fof(f2998,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k2_relat_1(sK3)) )
    | ~ spl8_144
    | ~ spl8_148 ),
    inference(resolution,[],[f2273,f2078])).

fof(f2078,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,X0),sK3)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_144 ),
    inference(avatar_component_clause,[],[f2077])).

fof(f2077,plain,
    ( spl8_144
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(k4_tarski(X0,X0),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_144])])).

fof(f2273,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k4_tarski(X1,X2),sK3)
        | r2_hidden(X2,k2_relat_1(sK3)) )
    | ~ spl8_148 ),
    inference(resolution,[],[f2249,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',t20_relat_1)).

fof(f2249,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_148 ),
    inference(avatar_component_clause,[],[f2248])).

fof(f2248,plain,
    ( spl8_148
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_148])])).

fof(f2357,plain,
    ( spl8_142
    | spl8_144 ),
    inference(avatar_split_clause,[],[f2205,f2077,f2074])).

fof(f2074,plain,
    ( spl8_142
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).

fof(f2205,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(k4_tarski(X0,X0),sK3)
      | o_0_0_xboole_0 = sK3 ) ),
    inference(resolution,[],[f1632,f124])).

fof(f124,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,X4)
      | r2_hidden(X3,X4)
      | o_0_0_xboole_0 = X4 ) ),
    inference(resolution,[],[f80,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f117,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',t6_boole)).

fof(f117,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f70,f68])).

fof(f68,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',dt_o_0_0_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',t2_subset)).

fof(f1632,plain,(
    ! [X0] :
      ( m1_subset_1(k4_tarski(X0,X0),sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f1623,f114])).

fof(f114,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0) ) ),
    inference(global_subsumption,[],[f69,f98])).

fof(f98,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(X5,X5),k6_relat_1(X0))
      | ~ r2_hidden(X5,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X5),X1)
      | ~ r2_hidden(X5,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | X4 != X5
      | ~ r2_hidden(X4,X0)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK5(X0,X1) != sK6(X0,X1)
              | ~ r2_hidden(sK5(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
            & ( ( sK5(X0,X1) = sK6(X0,X1)
                & r2_hidden(sK5(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK5(X0,X1) != sK6(X0,X1)
          | ~ r2_hidden(sK5(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
        & ( ( sK5(X0,X1) = sK6(X0,X1)
            & r2_hidden(sK5(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',d10_relat_1)).

fof(f69,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',dt_k6_relat_1)).

fof(f1623,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_relat_1(sK2))
      | m1_subset_1(X0,sK3) ) ),
    inference(resolution,[],[f385,f66])).

fof(f66,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f385,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f95,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',t3_subset)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',t4_subset)).

fof(f2355,plain,
    ( spl8_3
    | ~ spl8_142 ),
    inference(avatar_contradiction_clause,[],[f2354])).

fof(f2354,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_142 ),
    inference(subsumption_resolution,[],[f213,f2119])).

fof(f2119,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl8_142 ),
    inference(resolution,[],[f2117,f114])).

fof(f2117,plain,
    ( ! [X0] : ~ r2_hidden(X0,k6_relat_1(sK2))
    | ~ spl8_142 ),
    inference(resolution,[],[f2080,f838])).

fof(f838,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,o_0_0_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f180,f85])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f96,f68])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',t5_subset)).

fof(f2080,plain,
    ( r1_tarski(k6_relat_1(sK2),o_0_0_xboole_0)
    | ~ spl8_142 ),
    inference(backward_demodulation,[],[f2075,f66])).

fof(f2075,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl8_142 ),
    inference(avatar_component_clause,[],[f2074])).

fof(f213,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f212,f71])).

fof(f71,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',existence_m1_subset_1)).

fof(f212,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | r2_hidden(X0,sK2) )
    | ~ spl8_3 ),
    inference(resolution,[],[f211,f80])).

fof(f211,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f205,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t30_relset_1.p',t7_boole)).

fof(f205,plain,
    ( r2_hidden(sK7(sK2,k2_relset_1(sK0,sK1,sK3)),sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f112,f82])).

fof(f2256,plain,
    ( ~ spl8_149
    | spl8_150
    | ~ spl8_144 ),
    inference(avatar_split_clause,[],[f2241,f2077,f2254,f2251])).

fof(f2241,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k1_relat_1(sK3))
        | ~ v1_relat_1(sK3) )
    | ~ spl8_144 ),
    inference(resolution,[],[f2078,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f2131,plain,
    ( spl8_1
    | ~ spl8_142 ),
    inference(avatar_contradiction_clause,[],[f2126])).

fof(f2126,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_142 ),
    inference(resolution,[],[f2119,f144])).

fof(f144,plain,
    ( r2_hidden(sK7(sK2,o_0_0_xboole_0),sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f143,f68])).

fof(f143,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(X4)
        | r2_hidden(sK7(sK2,X4),sK2) )
    | ~ spl8_1 ),
    inference(resolution,[],[f137,f87])).

fof(f137,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2),X0)
        | r2_hidden(sK7(sK2,X0),sK2) )
    | ~ spl8_1 ),
    inference(resolution,[],[f136,f82])).

fof(f136,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK2,X1)
        | r2_hidden(sK4(sK2),X1) )
    | ~ spl8_1 ),
    inference(resolution,[],[f81,f130])).

fof(f130,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f129,f71])).

fof(f129,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK2)
        | r2_hidden(X0,sK2) )
    | ~ spl8_1 ),
    inference(resolution,[],[f128,f80])).

fof(f128,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f125,f87])).

fof(f125,plain,
    ( r2_hidden(sK7(sK2,k1_relset_1(sK0,sK1,sK3)),sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f82,f106])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f113,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f67,f111,f105])).

fof(f67,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
