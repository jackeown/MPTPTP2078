%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t40_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:45 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  251 (1307 expanded)
%              Number of leaves         :   61 ( 433 expanded)
%              Depth                    :   19
%              Number of atoms          :  724 (3669 expanded)
%              Number of equality atoms :   37 ( 252 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f760,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f97,f104,f111,f118,f128,f144,f155,f176,f188,f199,f206,f216,f232,f254,f263,f331,f439,f445,f449,f450,f464,f489,f492,f553,f572,f605,f615,f616,f617,f621,f625,f626,f630,f631,f641,f706,f710,f735,f757])).

fof(f757,plain,
    ( ~ spl7_2
    | ~ spl7_4
    | spl7_41 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f751,f96])).

fof(f96,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f751,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl7_4
    | ~ spl7_41 ),
    inference(resolution,[],[f746,f330])).

fof(f330,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl7_41
  <=> ~ r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f746,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f745,f103])).

fof(f103,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f745,plain,
    ( ! [X0] :
        ( r2_relset_1(sK0,sK1,k7_relat_1(sK3,X0),sK3)
        | ~ r1_tarski(sK0,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl7_4 ),
    inference(superposition,[],[f65,f740])).

fof(f740,plain,
    ( ! [X14] : k7_relat_1(sK3,X14) = k5_relset_1(sK0,sK1,sK3,X14)
    | ~ spl7_4 ),
    inference(resolution,[],[f70,f103])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',redefinition_k5_relset_1)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',t34_relset_1)).

fof(f735,plain,
    ( spl7_22
    | ~ spl7_14
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f732,f558,f142,f186])).

fof(f186,plain,
    ( spl7_22
  <=> k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f142,plain,
    ( spl7_14
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f558,plain,
    ( spl7_56
  <=> v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f732,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl7_14
    | ~ spl7_56 ),
    inference(resolution,[],[f711,f559])).

fof(f559,plain,
    ( v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f558])).

fof(f711,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = X0 )
    | ~ spl7_14 ),
    inference(resolution,[],[f143,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',t8_boole)).

fof(f143,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f710,plain,
    ( spl7_78
    | spl7_82
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f699,f443,f116,f102,f708,f701])).

fof(f701,plain,
    ( spl7_78
  <=> ! [X27,X28] : m1_subset_1(k7_relat_1(k7_relat_1(sK3,X27),X28),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f708,plain,
    ( spl7_82
  <=> ! [X29,X30] :
        ( v1_xboole_0(k7_relat_1(k7_relat_1(sK3,X29),X30))
        | ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k7_relat_1(k7_relat_1(sK3,X29),X30)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f116,plain,
    ( spl7_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f443,plain,
    ( spl7_46
  <=> ! [X16,X15] : r2_hidden(k7_relat_1(k7_relat_1(sK3,X15),X16),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f699,plain,
    ( ! [X30,X31,X29,X32] :
        ( v1_xboole_0(k7_relat_1(k7_relat_1(sK3,X29),X30))
        | ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k7_relat_1(k7_relat_1(sK3,X29),X30))
        | m1_subset_1(k7_relat_1(k7_relat_1(sK3,X31),X32),k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_46 ),
    inference(resolution,[],[f528,f408])).

fof(f408,plain,
    ( ! [X10,X8,X9] :
        ( ~ r2_hidden(X8,k7_relat_1(k7_relat_1(sK3,X9),X10))
        | m1_subset_1(X8,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f401,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',t4_subset)).

fof(f401,plain,
    ( ! [X0,X1] : m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f400,f324])).

fof(f324,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK3,X0))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f322,f271])).

fof(f271,plain,
    ( ! [X0] : v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f268,f117])).

fof(f117,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | v1_funct_1(k2_partfun1(sK0,sK1,sK3,X0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f62,f103])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',dt_k2_partfun1)).

fof(f322,plain,
    ( ! [X0] : k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f317,f117])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3)
        | k2_partfun1(sK0,sK1,sK3,X0) = k7_relat_1(sK3,X0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f64,f103])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',redefinition_k2_partfun1)).

fof(f400,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(k7_relat_1(sK3,X0)) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f398,f368])).

fof(f368,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f367,f117])).

fof(f367,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f364,f103])).

fof(f364,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(superposition,[],[f63,f322])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f398,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(k7_relat_1(sK3,X0)) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(superposition,[],[f63,f377])).

fof(f377,plain,
    ( ! [X0,X1] : k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1)
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f369,f324])).

fof(f369,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X0))
        | k2_partfun1(sK0,sK1,k7_relat_1(sK3,X0),X1) = k7_relat_1(k7_relat_1(sK3,X0),X1) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f368,f64])).

fof(f528,plain,
    ( ! [X33,X31,X32] :
        ( r2_hidden(k7_relat_1(k7_relat_1(sK3,X32),X33),X31)
        | v1_xboole_0(X31)
        | ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),X31) )
    | ~ spl7_46 ),
    inference(resolution,[],[f515,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',t2_subset)).

fof(f515,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),X2)
        | ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),X2) )
    | ~ spl7_46 ),
    inference(resolution,[],[f444,f238])).

fof(f238,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | m1_subset_1(X3,X5)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f75,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',t3_subset)).

fof(f444,plain,
    ( ! [X15,X16] : r2_hidden(k7_relat_1(k7_relat_1(sK3,X15),X16),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f443])).

fof(f706,plain,
    ( spl7_78
    | spl7_80
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f698,f443,f116,f102,f704,f701])).

fof(f704,plain,
    ( spl7_80
  <=> ! [X26] :
        ( v1_xboole_0(k7_relat_1(sK3,X26))
        | ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k7_relat_1(sK3,X26)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f698,plain,
    ( ! [X28,X26,X27] :
        ( v1_xboole_0(k7_relat_1(sK3,X26))
        | ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k7_relat_1(sK3,X26))
        | m1_subset_1(k7_relat_1(k7_relat_1(sK3,X27),X28),k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_46 ),
    inference(resolution,[],[f528,f373])).

fof(f373,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k7_relat_1(sK3,X6))
        | m1_subset_1(X5,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f368,f75])).

fof(f641,plain,
    ( spl7_76
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f634,f168,f639])).

fof(f639,plain,
    ( spl7_76
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f168,plain,
    ( spl7_18
  <=> sP6(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f634,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f169,f159])).

fof(f159,plain,(
    ! [X2] :
      ( ~ sP6(X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f130,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP6(X1) ) ),
    inference(general_splitting,[],[f72,f81_D])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP6(X1) ) ),
    inference(cnf_transformation,[],[f81_D])).

fof(f81_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP6(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',t5_subset)).

fof(f130,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f74,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',existence_m1_subset_1)).

fof(f169,plain,
    ( sP6(sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f631,plain,
    ( ~ spl7_21
    | spl7_18
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f218,f126,f168,f174])).

fof(f174,plain,
    ( spl7_21
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f126,plain,
    ( spl7_10
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f218,plain,
    ( sP6(sK3)
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_10 ),
    inference(resolution,[],[f163,f127])).

fof(f127,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f126])).

fof(f163,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | sP6(X2)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f81,f66])).

fof(f630,plain,
    ( spl7_20
    | spl7_74
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f239,f102,f628,f171])).

fof(f171,plain,
    ( spl7_20
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f628,plain,
    ( spl7_74
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f236,f74])).

fof(f236,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f75,f103])).

fof(f626,plain,
    ( spl7_72
    | ~ spl7_21
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f374,f116,f102,f174,f623])).

fof(f623,plain,
    ( spl7_72
  <=> ! [X1] : sP6(k7_relat_1(sK3,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f374,plain,
    ( ! [X7] :
        ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | sP6(k7_relat_1(sK3,X7)) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f368,f81])).

fof(f625,plain,
    ( ~ spl7_21
    | spl7_72
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f381,f116,f102,f623,f174])).

fof(f381,plain,
    ( ! [X1] :
        ( sP6(k7_relat_1(sK3,X1))
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f375,f163])).

fof(f375,plain,
    ( ! [X8] : r1_tarski(k7_relat_1(sK3,X8),k2_zfmisc_1(sK0,sK1))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f368,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f621,plain,
    ( spl7_20
    | spl7_70
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f390,f116,f102,f619,f171])).

fof(f619,plain,
    ( spl7_70
  <=> ! [X0] :
        ( v1_xboole_0(k7_relat_1(sK3,X0))
        | r2_hidden(sK4(k7_relat_1(sK3,X0)),k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f390,plain,
    ( ! [X0] :
        ( v1_xboole_0(k7_relat_1(sK3,X0))
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | r2_hidden(sK4(k7_relat_1(sK3,X0)),k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f387,f74])).

fof(f387,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(k7_relat_1(sK3,X0)),k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(k7_relat_1(sK3,X0)) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f373,f130])).

fof(f617,plain,
    ( spl7_42
    | ~ spl7_21
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f409,f116,f102,f174,f434])).

fof(f434,plain,
    ( spl7_42
  <=> ! [X5,X6] : sP6(k7_relat_1(k7_relat_1(sK3,X5),X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f409,plain,
    ( ! [X12,X11] :
        ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | sP6(k7_relat_1(k7_relat_1(sK3,X11),X12)) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f401,f81])).

fof(f616,plain,
    ( ~ spl7_21
    | spl7_42
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f416,f116,f102,f434,f174])).

fof(f416,plain,
    ( ! [X2,X3] :
        ( sP6(k7_relat_1(k7_relat_1(sK3,X2),X3))
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f410,f163])).

fof(f410,plain,
    ( ! [X14,X13] : r1_tarski(k7_relat_1(k7_relat_1(sK3,X13),X14),k2_zfmisc_1(sK0,sK1))
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f401,f67])).

fof(f615,plain,
    ( ~ spl7_67
    | spl7_68
    | ~ spl7_4
    | ~ spl7_8
    | spl7_21 ),
    inference(avatar_split_clause,[],[f597,f174,f116,f102,f613,f610])).

fof(f610,plain,
    ( spl7_67
  <=> ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f613,plain,
    ( spl7_68
  <=> ! [X29] :
        ( v1_xboole_0(k7_relat_1(sK3,X29))
        | ~ r2_relset_1(sK0,sK1,sK4(k7_relat_1(sK3,X29)),sK3)
        | sK3 = sK4(k7_relat_1(sK3,X29)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f597,plain,
    ( ! [X29] :
        ( v1_xboole_0(k7_relat_1(sK3,X29))
        | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK3 = sK4(k7_relat_1(sK3,X29))
        | ~ r2_relset_1(sK0,sK1,sK4(k7_relat_1(sK3,X29)),sK3) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_21 ),
    inference(resolution,[],[f392,f500])).

fof(f500,plain,
    ( ! [X14] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK3 = X14
        | ~ r2_relset_1(sK0,sK1,X14,sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f59,f103])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',redefinition_r2_relset_1)).

fof(f392,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(k7_relat_1(sK3,X0)),X1)
        | v1_xboole_0(k7_relat_1(sK3,X0))
        | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),X1) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_21 ),
    inference(resolution,[],[f391,f238])).

fof(f391,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k7_relat_1(sK3,X0)),k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(k7_relat_1(sK3,X0)) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f390,f175])).

fof(f175,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f174])).

fof(f605,plain,
    ( spl7_62
    | spl7_64
    | ~ spl7_4
    | ~ spl7_8
    | spl7_21 ),
    inference(avatar_split_clause,[],[f589,f174,f116,f102,f603,f600])).

fof(f600,plain,
    ( spl7_62
  <=> ! [X4] :
        ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(X4))
        | ~ v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f603,plain,
    ( spl7_64
  <=> ! [X3] :
        ( v1_xboole_0(k7_relat_1(sK3,X3))
        | sP6(sK4(k7_relat_1(sK3,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f589,plain,
    ( ! [X4,X3] :
        ( v1_xboole_0(k7_relat_1(sK3,X3))
        | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k1_zfmisc_1(X4))
        | ~ v1_xboole_0(X4)
        | sP6(sK4(k7_relat_1(sK3,X3))) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_21 ),
    inference(resolution,[],[f392,f81])).

fof(f572,plain,
    ( spl7_56
    | ~ spl7_59
    | spl7_60
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f539,f102,f570,f564,f558])).

fof(f564,plain,
    ( spl7_59
  <=> ~ r2_relset_1(sK0,sK1,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f570,plain,
    ( spl7_60
  <=> sK3 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f539,plain,
    ( sK3 = sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ r2_relset_1(sK0,sK1,sK4(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK3)
    | v1_xboole_0(sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ spl7_4 ),
    inference(resolution,[],[f500,f264])).

fof(f264,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(sK4(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK4(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f237,f130])).

fof(f237,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK4(k1_zfmisc_1(X2)))
      | m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f75,f68])).

fof(f553,plain,
    ( ~ spl7_53
    | spl7_54
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f537,f102,f551,f545])).

fof(f545,plain,
    ( spl7_53
  <=> ~ r2_relset_1(sK0,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f551,plain,
    ( spl7_54
  <=> sK3 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f537,plain,
    ( sK3 = sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK1,sK4(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f500,f68])).

fof(f492,plain,
    ( ~ spl7_14
    | ~ spl7_22
    | spl7_27 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_22
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f490,f143])).

fof(f490,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_22
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f468,f205])).

fof(f205,plain,
    ( ~ sP6(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl7_27
  <=> ~ sP6(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f468,plain,
    ( sP6(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_22 ),
    inference(superposition,[],[f162,f187])).

fof(f187,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f186])).

fof(f162,plain,(
    ! [X0] :
      ( sP6(sK4(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f81,f68])).

fof(f489,plain,
    ( spl7_50
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f467,f186,f487])).

fof(f487,plain,
    ( spl7_50
  <=> r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f467,plain,
    ( r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_22 ),
    inference(superposition,[],[f120,f187])).

fof(f120,plain,(
    ! [X0] : r1_tarski(sK4(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f67,f68])).

fof(f464,plain,
    ( spl7_22
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f463,f142,f186])).

fof(f463,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl7_14 ),
    inference(resolution,[],[f457,f143])).

fof(f457,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(X1)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK4(k1_zfmisc_1(X1)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f454,f177])).

fof(f177,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f162,f159])).

fof(f454,plain,
    ( ! [X3] :
        ( ~ v1_xboole_0(X3)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = X3 )
    | ~ spl7_14 ),
    inference(resolution,[],[f143,f69])).

fof(f450,plain,
    ( ~ spl7_15
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f192,f136,f139])).

fof(f139,plain,
    ( spl7_15
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f136,plain,
    ( spl7_12
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f192,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12 ),
    inference(resolution,[],[f137,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',t7_boole)).

fof(f137,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f449,plain,
    ( spl7_48
    | spl7_14
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f376,f116,f102,f142,f447])).

fof(f447,plain,
    ( spl7_48
  <=> ! [X9] : r2_hidden(k7_relat_1(sK3,X9),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f376,plain,
    ( ! [X9] :
        ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | r2_hidden(k7_relat_1(sK3,X9),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f368,f74])).

fof(f445,plain,
    ( spl7_46
    | spl7_14
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f411,f116,f102,f142,f443])).

fof(f411,plain,
    ( ! [X15,X16] :
        ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | r2_hidden(k7_relat_1(k7_relat_1(sK3,X15),X16),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(resolution,[],[f401,f74])).

fof(f439,plain,
    ( spl7_42
    | spl7_44
    | ~ spl7_4
    | ~ spl7_8
    | spl7_15 ),
    inference(avatar_split_clause,[],[f426,f139,f116,f102,f437,f434])).

fof(f437,plain,
    ( spl7_44
  <=> ! [X4] :
        ( ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(X4))
        | ~ v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f426,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),k1_zfmisc_1(X4))
        | ~ v1_xboole_0(X4)
        | sP6(k7_relat_1(k7_relat_1(sK3,X5),X6)) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(resolution,[],[f417,f81])).

fof(f417,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k7_relat_1(k7_relat_1(sK3,X0),X1),X2)
        | ~ r1_tarski(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),X2) )
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(resolution,[],[f414,f238])).

fof(f414,plain,
    ( ! [X15,X16] : r2_hidden(k7_relat_1(k7_relat_1(sK3,X15),X16),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f411,f140])).

fof(f140,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f331,plain,
    ( ~ spl7_41
    | spl7_1
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f323,f116,f102,f88,f329])).

fof(f88,plain,
    ( spl7_1
  <=> ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f323,plain,
    ( ~ r2_relset_1(sK0,sK1,k7_relat_1(sK3,sK2),sK3)
    | ~ spl7_1
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f322,f89])).

fof(f89,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f263,plain,
    ( ~ spl7_39
    | ~ spl7_4
    | spl7_21 ),
    inference(avatar_split_clause,[],[f256,f174,f102,f261])).

fof(f261,plain,
    ( spl7_39
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f256,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3)
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3)
    | ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3)
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(resolution,[],[f241,f240])).

fof(f240,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f239,f175])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),X0)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(resolution,[],[f240,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',antisymmetry_r2_hidden)).

fof(f254,plain,
    ( ~ spl7_35
    | spl7_36
    | ~ spl7_4
    | spl7_21 ),
    inference(avatar_split_clause,[],[f243,f174,f102,f252,f249])).

fof(f249,plain,
    ( spl7_35
  <=> ~ sP6(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f252,plain,
    ( spl7_36
  <=> ! [X2] : ~ r2_hidden(X2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f243,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK3)
        | ~ sP6(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(resolution,[],[f240,f82])).

fof(f232,plain,
    ( ~ spl7_31
    | spl7_32
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f217,f95,f230,f224])).

fof(f224,plain,
    ( spl7_31
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f230,plain,
    ( spl7_32
  <=> sP6(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f217,plain,
    ( sP6(sK0)
    | ~ v1_xboole_0(sK2)
    | ~ spl7_2 ),
    inference(resolution,[],[f163,f96])).

fof(f216,plain,
    ( spl7_28
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f207,f102,f214])).

fof(f214,plain,
    ( spl7_28
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f207,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f83,f103])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f206,plain,
    ( ~ spl7_27
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f191,f136,f204])).

fof(f191,plain,
    ( ~ sP6(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_12 ),
    inference(resolution,[],[f137,f82])).

fof(f199,plain,
    ( ~ spl7_25
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f189,f136,f197])).

fof(f197,plain,
    ( spl7_25
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f189,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK3)
    | ~ spl7_12 ),
    inference(resolution,[],[f137,f77])).

fof(f188,plain,
    ( spl7_22
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f180,f142,f186])).

fof(f180,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK4(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl7_14 ),
    inference(resolution,[],[f178,f143])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = sK4(k1_zfmisc_1(X0)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f177,f145])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = X0 )
    | ~ spl7_14 ),
    inference(resolution,[],[f143,f69])).

fof(f176,plain,
    ( spl7_18
    | ~ spl7_21
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f161,f102,f174,f168])).

fof(f161,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | sP6(sK3)
    | ~ spl7_4 ),
    inference(resolution,[],[f81,f103])).

fof(f155,plain,
    ( ~ spl7_17
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f146,f102,f153])).

fof(f153,plain,
    ( spl7_17
  <=> ~ sP5(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f146,plain,
    ( ~ sP5(sK1,sK0)
    | ~ spl7_4 ),
    inference(resolution,[],[f80,f103])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP5(X1,X0) ) ),
    inference(general_splitting,[],[f61,f79_D])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP5(X1,X0) ) ),
    inference(cnf_transformation,[],[f79_D])).

fof(f79_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP5(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',reflexivity_r2_relset_1)).

fof(f144,plain,
    ( spl7_12
    | spl7_14
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f129,f102,f142,f136])).

fof(f129,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_4 ),
    inference(resolution,[],[f74,f103])).

fof(f128,plain,
    ( spl7_10
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f119,f102,f126])).

fof(f119,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl7_4 ),
    inference(resolution,[],[f67,f103])).

fof(f118,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f53,f116])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t40_funct_2.p',t40_funct_2)).

fof(f111,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f54,f109])).

fof(f109,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f54,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f55,f102])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f97,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f56,f95])).

fof(f56,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f57,f88])).

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
