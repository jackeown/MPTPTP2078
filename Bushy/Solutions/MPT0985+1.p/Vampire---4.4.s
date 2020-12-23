%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t31_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:43 EDT 2019

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  269 ( 926 expanded)
%              Number of leaves         :   50 ( 285 expanded)
%              Depth                    :   15
%              Number of atoms          :  772 (3883 expanded)
%              Number of equality atoms :  116 ( 657 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f203,f292,f302,f304,f306,f346,f378,f388,f442,f724,f989,f5620,f5720,f5820,f6330,f6506,f6548,f7100,f7244,f8061,f9081,f9088,f11314,f11316,f14114,f14239,f14241,f14293,f14348,f14965,f15064,f15444])).

fof(f15444,plain,
    ( spl7_5
    | ~ spl7_8
    | ~ spl7_48
    | ~ spl7_160 ),
    inference(avatar_contradiction_clause,[],[f15441])).

fof(f15441,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_48
    | ~ spl7_160 ),
    inference(resolution,[],[f15067,f9953])).

fof(f9953,plain,(
    ! [X3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) ),
    inference(superposition,[],[f110,f9841])).

fof(f9841,plain,(
    ! [X0] : k1_xboole_0 = sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(resolution,[],[f9789,f5607])).

fof(f5607,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f5606,f88])).

fof(f88,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',dt_o_0_0_xboole_0)).

fof(f5606,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(resolution,[],[f88,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',t6_boole)).

fof(f9789,plain,(
    ! [X10,X11] :
      ( ~ v1_xboole_0(X10)
      | k1_xboole_0 = sK5(k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    inference(resolution,[],[f9754,f89])).

fof(f9754,plain,(
    ! [X8,X9] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(k2_zfmisc_1(X8,X9))))
      | ~ v1_xboole_0(X8) ) ),
    inference(resolution,[],[f111,f110])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',cc3_relset_1)).

fof(f110,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',existence_m1_subset_1)).

fof(f15067,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_48
    | ~ spl7_160 ),
    inference(forward_demodulation,[],[f15066,f6489])).

fof(f6489,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0
    | ~ spl7_160 ),
    inference(resolution,[],[f985,f89])).

fof(f985,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl7_160 ),
    inference(avatar_component_clause,[],[f984])).

fof(f984,plain,
    ( spl7_160
  <=> v1_xboole_0(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).

fof(f15066,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_48 ),
    inference(forward_demodulation,[],[f15065,f333])).

fof(f333,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl7_48
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f15065,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl7_5
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f158,f175])).

fof(f175,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f158,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_5
  <=> ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f15064,plain,
    ( spl7_3
    | ~ spl7_8
    | ~ spl7_48
    | ~ spl7_160
    | ~ spl7_164 ),
    inference(avatar_contradiction_clause,[],[f15063])).

fof(f15063,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_48
    | ~ spl7_160
    | ~ spl7_164 ),
    inference(resolution,[],[f15062,f13494])).

fof(f13494,plain,
    ( ! [X1] : v1_funct_2(k1_xboole_0,k1_xboole_0,X1)
    | ~ spl7_164 ),
    inference(trivial_inequality_removal,[],[f13493])).

fof(f13493,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X1) )
    | ~ spl7_164 ),
    inference(forward_demodulation,[],[f9964,f9984])).

fof(f9984,plain,
    ( ! [X5] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X5,k1_xboole_0)
    | ~ spl7_164 ),
    inference(forward_demodulation,[],[f9969,f9108])).

fof(f9108,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_164 ),
    inference(resolution,[],[f1002,f89])).

fof(f1002,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl7_164 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f1001,plain,
    ( spl7_164
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_164])])).

fof(f9969,plain,(
    ! [X5] : k1_relset_1(k1_xboole_0,X5,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f9953,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',redefinition_k1_relset_1)).

fof(f9964,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X1) ) ),
    inference(resolution,[],[f9953,f148])).

fof(f148,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',d1_funct_2)).

fof(f15062,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_48
    | ~ spl7_160 ),
    inference(forward_demodulation,[],[f15028,f6489])).

fof(f15028,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_48 ),
    inference(backward_demodulation,[],[f333,f14792])).

fof(f14792,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f175,f155])).

fof(f155,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_3
  <=> ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f14965,plain,
    ( spl7_48
    | spl7_50
    | ~ spl7_53
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f14954,f174,f338,f335,f332])).

fof(f335,plain,
    ( spl7_50
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f338,plain,
    ( spl7_53
  <=> ~ v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f14954,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl7_8 ),
    inference(resolution,[],[f14790,f147])).

fof(f147,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f14790,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f175,f84])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f67])).

fof(f67,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',t31_funct_2)).

fof(f14348,plain,
    ( ~ spl7_13
    | spl7_28 ),
    inference(avatar_split_clause,[],[f8087,f244,f241])).

fof(f241,plain,
    ( spl7_13
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f244,plain,
    ( spl7_28
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f8087,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK2) ),
    inference(superposition,[],[f90,f216])).

fof(f216,plain,(
    k2_relat_1(sK2) = sK1 ),
    inference(forward_demodulation,[],[f162,f86])).

fof(f86,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f68])).

fof(f162,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f84,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',redefinition_k2_relset_1)).

fof(f90,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',fc11_relat_1)).

fof(f14293,plain,
    ( spl7_6
    | spl7_8 ),
    inference(avatar_split_clause,[],[f14292,f174,f171])).

fof(f171,plain,
    ( spl7_6
  <=> k1_relset_1(sK0,sK1,sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f14292,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(global_subsumption,[],[f9009])).

fof(f9009,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(global_subsumption,[],[f83,f9000])).

fof(f9000,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(resolution,[],[f84,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f83,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f14241,plain,
    ( spl7_5
    | ~ spl7_20
    | ~ spl7_772 ),
    inference(avatar_contradiction_clause,[],[f14240])).

fof(f14240,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_20
    | ~ spl7_772 ),
    inference(subsumption_resolution,[],[f14096,f158])).

fof(f14096,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_20
    | ~ spl7_772 ),
    inference(resolution,[],[f8708,f11331])).

fof(f11331,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl7_20 ),
    inference(resolution,[],[f214,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',t3_subset)).

fof(f214,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl7_20
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f8708,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl7_772 ),
    inference(resolution,[],[f8183,f201])).

fof(f201,plain,(
    r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f192,f118])).

fof(f192,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(global_subsumption,[],[f84,f191])).

fof(f191,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f126,f86])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',dt_k2_relset_1)).

fof(f8183,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(sK1,X3)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ r1_tarski(sK0,X2) )
    | ~ spl7_772 ),
    inference(avatar_component_clause,[],[f8182])).

fof(f8182,plain,
    ( spl7_772
  <=> ! [X3,X2] :
        ( ~ r1_tarski(sK1,X3)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ r1_tarski(sK0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_772])])).

fof(f14239,plain,
    ( ~ spl7_20
    | ~ spl7_772
    | spl7_1165 ),
    inference(avatar_contradiction_clause,[],[f14236])).

fof(f14236,plain,
    ( $false
    | ~ spl7_20
    | ~ spl7_772
    | ~ spl7_1165 ),
    inference(subsumption_resolution,[],[f14113,f14116])).

fof(f14116,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | ~ spl7_20
    | ~ spl7_772 ),
    inference(forward_demodulation,[],[f14102,f297])).

fof(f297,plain,(
    k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_subsumption,[],[f82,f85,f296])).

fof(f296,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f293,f216])).

fof(f293,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(resolution,[],[f164,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',t55_funct_1)).

fof(f164,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f84,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',cc1_relset_1)).

fof(f85,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f14102,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl7_20
    | ~ spl7_772 ),
    inference(resolution,[],[f14096,f124])).

fof(f14113,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | ~ spl7_1165 ),
    inference(avatar_component_clause,[],[f14112])).

fof(f14112,plain,
    ( spl7_1165
  <=> k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1165])])).

fof(f14114,plain,
    ( spl7_2
    | spl7_50
    | ~ spl7_1165
    | ~ spl7_20
    | ~ spl7_772 ),
    inference(avatar_split_clause,[],[f14100,f8182,f213,f14112,f335,f14109])).

fof(f14109,plain,
    ( spl7_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f14100,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) != sK1
    | k1_xboole_0 = sK0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl7_20
    | ~ spl7_772 ),
    inference(resolution,[],[f14096,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f11316,plain,(
    spl7_19 ),
    inference(avatar_contradiction_clause,[],[f11315])).

fof(f11315,plain,
    ( $false
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f84,f211])).

fof(f211,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl7_19
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f11314,plain,
    ( ~ spl7_19
    | spl7_20
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f9058,f171,f213,f210])).

fof(f9058,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_6 ),
    inference(superposition,[],[f127,f172])).

fof(f172,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f171])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',dt_k1_relset_1)).

fof(f9088,plain,
    ( ~ spl7_113
    | spl7_164
    | ~ spl7_60
    | ~ spl7_160 ),
    inference(avatar_split_clause,[],[f9082,f984,f370,f1001,f728])).

fof(f728,plain,
    ( spl7_113
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f370,plain,
    ( spl7_60
  <=> k1_relat_1(k2_funct_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f9082,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_60
    | ~ spl7_160 ),
    inference(superposition,[],[f90,f7947])).

fof(f7947,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl7_60
    | ~ spl7_160 ),
    inference(forward_demodulation,[],[f371,f6489])).

fof(f371,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f370])).

fof(f9081,plain,
    ( ~ spl7_23
    | spl7_772
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f9080,f300,f8182,f226])).

fof(f226,plain,
    ( spl7_23
  <=> ~ v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f300,plain,
    ( spl7_46
  <=> k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f9080,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(sK1,X3)
        | ~ r1_tarski(sK0,X2)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f9077,f297])).

fof(f9077,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(sK0,X2)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ r1_tarski(k1_relat_1(k2_funct_1(sK2)),X3)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl7_46 ),
    inference(superposition,[],[f122,f301])).

fof(f301,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f300])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',t11_relset_1)).

fof(f8061,plain,
    ( spl7_13
    | ~ spl7_48 ),
    inference(avatar_contradiction_clause,[],[f8060])).

fof(f8060,plain,
    ( $false
    | ~ spl7_13
    | ~ spl7_48 ),
    inference(subsumption_resolution,[],[f5607,f8054])).

fof(f8054,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_13
    | ~ spl7_48 ),
    inference(forward_demodulation,[],[f242,f333])).

fof(f242,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f241])).

fof(f7244,plain,
    ( spl7_5
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_50
    | ~ spl7_160 ),
    inference(avatar_contradiction_clause,[],[f7243])).

fof(f7243,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_50
    | ~ spl7_160 ),
    inference(subsumption_resolution,[],[f6545,f7104])).

fof(f7104,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_50
    | ~ spl7_160 ),
    inference(forward_demodulation,[],[f7103,f6489])).

fof(f7103,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f7102,f5859])).

fof(f5859,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_12 ),
    inference(resolution,[],[f182,f89])).

fof(f182,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_12
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f7102,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_5
    | ~ spl7_28
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f7101,f5901])).

fof(f5901,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_28 ),
    inference(resolution,[],[f245,f89])).

fof(f245,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f7101,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl7_5
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f158,f336])).

fof(f336,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f335])).

fof(f6545,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_50 ),
    inference(backward_demodulation,[],[f5901,f5918])).

fof(f5918,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_12
    | ~ spl7_50 ),
    inference(backward_demodulation,[],[f5859,f648])).

fof(f648,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f84,f336])).

fof(f7100,plain,
    ( spl7_3
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_50
    | ~ spl7_160 ),
    inference(avatar_contradiction_clause,[],[f7099])).

fof(f7099,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_50
    | ~ spl7_160 ),
    inference(subsumption_resolution,[],[f6546,f7092])).

fof(f7092,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_50
    | ~ spl7_160 ),
    inference(backward_demodulation,[],[f6489,f6543])).

fof(f6543,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_50 ),
    inference(backward_demodulation,[],[f5901,f5916])).

fof(f5916,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),sK1,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_50 ),
    inference(backward_demodulation,[],[f5859,f646])).

fof(f646,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f155,f336])).

fof(f6546,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_50 ),
    inference(backward_demodulation,[],[f5901,f5919])).

fof(f5919,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1)
    | ~ spl7_12
    | ~ spl7_50 ),
    inference(backward_demodulation,[],[f5859,f649])).

fof(f649,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl7_50 ),
    inference(forward_demodulation,[],[f83,f336])).

fof(f6548,plain,
    ( spl7_9
    | ~ spl7_28 ),
    inference(avatar_contradiction_clause,[],[f6509])).

fof(f6509,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f1171,f5901])).

fof(f1171,plain,
    ( k1_xboole_0 != sK1
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f1170])).

fof(f1170,plain,
    ( spl7_9
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f6506,plain,
    ( ~ spl7_12
    | ~ spl7_28
    | spl7_163 ),
    inference(avatar_contradiction_clause,[],[f6505])).

fof(f6505,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_28
    | ~ spl7_163 ),
    inference(subsumption_resolution,[],[f245,f6492])).

fof(f6492,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl7_12
    | ~ spl7_163 ),
    inference(forward_demodulation,[],[f988,f5907])).

fof(f5907,plain,
    ( k2_relat_1(k1_xboole_0) = sK1
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f5859,f216])).

fof(f988,plain,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl7_163 ),
    inference(avatar_component_clause,[],[f987])).

fof(f987,plain,
    ( spl7_163
  <=> ~ v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_163])])).

fof(f6330,plain,
    ( ~ spl7_12
    | spl7_65 ),
    inference(avatar_contradiction_clause,[],[f6329])).

fof(f6329,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_65 ),
    inference(subsumption_resolution,[],[f377,f5903])).

fof(f5903,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f5859,f85])).

fof(f377,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl7_65
  <=> ~ v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f5820,plain,
    ( ~ spl7_113
    | spl7_12
    | ~ spl7_50 ),
    inference(avatar_split_clause,[],[f746,f335,f181,f728])).

fof(f746,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_50 ),
    inference(resolution,[],[f648,f111])).

fof(f5720,plain,
    ( ~ spl7_83
    | ~ spl7_63
    | spl7_87 ),
    inference(avatar_split_clause,[],[f990,f544,f373,f537])).

fof(f537,plain,
    ( spl7_83
  <=> ~ v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f373,plain,
    ( spl7_63
  <=> ~ v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f544,plain,
    ( spl7_87
  <=> ~ v1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f990,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_87 ),
    inference(resolution,[],[f545,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',dt_k2_funct_1)).

fof(f545,plain,
    ( ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl7_87 ),
    inference(avatar_component_clause,[],[f544])).

fof(f5620,plain,(
    spl7_113 ),
    inference(avatar_contradiction_clause,[],[f5615])).

fof(f5615,plain,
    ( $false
    | ~ spl7_113 ),
    inference(subsumption_resolution,[],[f729,f5607])).

fof(f729,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_113 ),
    inference(avatar_component_clause,[],[f728])).

fof(f989,plain,
    ( spl7_160
    | ~ spl7_87
    | ~ spl7_163
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f953,f370,f987,f544,f984])).

fof(f953,plain,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k2_funct_1(k1_xboole_0))
    | v1_xboole_0(k2_funct_1(k1_xboole_0))
    | ~ spl7_60 ),
    inference(superposition,[],[f91,f371])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t31_funct_2.p',fc8_relat_1)).

fof(f724,plain,
    ( ~ spl7_12
    | spl7_83 ),
    inference(avatar_contradiction_clause,[],[f720])).

fof(f720,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_83 ),
    inference(subsumption_resolution,[],[f538,f711])).

fof(f711,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f584,f164])).

fof(f584,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_12 ),
    inference(resolution,[],[f182,f89])).

fof(f538,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl7_83 ),
    inference(avatar_component_clause,[],[f537])).

fof(f442,plain,
    ( ~ spl7_8
    | spl7_53 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_53 ),
    inference(subsumption_resolution,[],[f308,f339])).

fof(f339,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f338])).

fof(f308,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f175,f83])).

fof(f388,plain,
    ( ~ spl7_12
    | spl7_63 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_63 ),
    inference(subsumption_resolution,[],[f357,f374])).

fof(f374,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ spl7_63 ),
    inference(avatar_component_clause,[],[f373])).

fof(f357,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f288,f82])).

fof(f288,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_12 ),
    inference(resolution,[],[f182,f89])).

fof(f378,plain,
    ( spl7_60
    | ~ spl7_63
    | ~ spl7_65
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f366,f181,f376,f373,f370])).

fof(f366,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | k1_relat_1(k2_funct_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | ~ spl7_12 ),
    inference(resolution,[],[f359,f94])).

fof(f359,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_12 ),
    inference(backward_demodulation,[],[f288,f164])).

fof(f346,plain,
    ( ~ spl7_31
    | ~ spl7_33
    | spl7_23 ),
    inference(avatar_split_clause,[],[f345,f226,f258,f255])).

fof(f255,plain,
    ( spl7_31
  <=> ~ v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f258,plain,
    ( spl7_33
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f345,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_23 ),
    inference(resolution,[],[f227,f92])).

fof(f227,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f226])).

fof(f306,plain,(
    spl7_35 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f85,f262])).

fof(f262,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl7_35
  <=> ~ v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f304,plain,(
    spl7_33 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f82,f259])).

fof(f259,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f258])).

fof(f302,plain,
    ( ~ spl7_33
    | ~ spl7_35
    | spl7_46
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f298,f171,f300,f261,f258])).

fof(f298,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f294,f247])).

fof(f247,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f163,f172])).

fof(f163,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f84,f124])).

fof(f294,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f164,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f292,plain,(
    spl7_31 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f164,f256])).

fof(f256,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f255])).

fof(f203,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f152,f198])).

fof(f198,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(global_subsumption,[],[f82,f195])).

fof(f195,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f164,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f152,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl7_1
  <=> ~ v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f159,plain,
    ( ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f87,f157,f154,f151])).

fof(f87,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f68])).
%------------------------------------------------------------------------------
