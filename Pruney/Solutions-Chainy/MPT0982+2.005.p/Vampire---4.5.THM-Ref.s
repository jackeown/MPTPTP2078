%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:27 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 788 expanded)
%              Number of leaves         :   36 ( 255 expanded)
%              Depth                    :   22
%              Number of atoms          :  799 (5410 expanded)
%              Number of equality atoms :  157 (1562 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1337,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f242,f291,f294,f354,f377,f545,f601,f774,f777,f815,f823,f930,f1336])).

fof(f1336,plain,
    ( ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_54
    | ~ spl9_58 ),
    inference(avatar_contradiction_clause,[],[f1335])).

fof(f1335,plain,
    ( $false
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_54
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f1334,f111])).

fof(f111,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f89,f65])).

fof(f65,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( sK5 != k2_relset_1(sK4,sK5,sK7)
    & k1_xboole_0 != sK6
    & v2_funct_1(sK8)
    & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f21,f52,f51])).

fof(f51,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( sK5 != k2_relset_1(sK4,sK5,sK7)
          & k1_xboole_0 != sK6
          & v2_funct_1(X4)
          & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X4,sK5,sK6)
          & v1_funct_1(X4) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X4] :
        ( sK5 != k2_relset_1(sK4,sK5,sK7)
        & k1_xboole_0 != sK6
        & v2_funct_1(X4)
        & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        & v1_funct_2(X4,sK5,sK6)
        & v1_funct_1(X4) )
   => ( sK5 != k2_relset_1(sK4,sK5,sK7)
      & k1_xboole_0 != sK6
      & v2_funct_1(sK8)
      & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8))
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1334,plain,
    ( ~ v1_relat_1(sK7)
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_54
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f1333,f124])).

fof(f124,plain,(
    v5_relat_1(sK7,sK5) ),
    inference(resolution,[],[f93,f65])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1333,plain,
    ( ~ v5_relat_1(sK7,sK5)
    | ~ v1_relat_1(sK7)
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_54
    | ~ spl9_58 ),
    inference(resolution,[],[f1211,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1211,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK5)
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_54
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f1210,f334])).

fof(f334,plain,
    ( sK5 = k2_relat_1(k2_funct_1(sK8))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl9_13
  <=> sK5 = k2_relat_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f1210,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8)))
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_54
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f1209,f147])).

fof(f147,plain,(
    sK5 != k2_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f136,f65])).

fof(f136,plain,
    ( sK5 != k2_relat_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(superposition,[],[f72,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f72,plain,(
    sK5 != k2_relset_1(sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f1209,plain,
    ( sK5 = k2_relat_1(sK7)
    | ~ r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8)))
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_54
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f1208,f931])).

fof(f931,plain,
    ( sK5 = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ spl9_13
    | ~ spl9_58 ),
    inference(backward_demodulation,[],[f814,f334])).

fof(f814,plain,
    ( k2_relat_1(k2_funct_1(sK8)) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f812])).

fof(f812,plain,
    ( spl9_58
  <=> k2_relat_1(k2_funct_1(sK8)) = k9_relat_1(k2_funct_1(sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f1208,plain,
    ( k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8)))
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f1207,f112])).

fof(f112,plain,(
    v1_relat_1(sK8) ),
    inference(resolution,[],[f89,f68])).

fof(f68,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f53])).

fof(f1207,plain,
    ( k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8)))
    | ~ v1_relat_1(sK8)
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f1206,f66])).

fof(f66,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f1206,plain,
    ( k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8)))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f1205,f70])).

fof(f70,plain,(
    v2_funct_1(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f1205,plain,
    ( k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8)))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f1204,f275])).

fof(f275,plain,
    ( v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl9_10
  <=> v1_relat_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f1204,plain,
    ( k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8)))
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_16
    | ~ spl9_54 ),
    inference(subsumption_resolution,[],[f1176,f795])).

fof(f795,plain,
    ( v1_funct_1(k2_funct_1(sK8))
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f794])).

fof(f794,plain,
    ( spl9_54
  <=> v1_funct_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f1176,plain,
    ( k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8)))
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_16 ),
    inference(superposition,[],[f170,f460])).

fof(f460,plain,
    ( sK6 = k9_relat_1(sK8,k2_relat_1(sK7))
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f459,f111])).

fof(f459,plain,
    ( sK6 = k9_relat_1(sK8,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f448,f112])).

fof(f448,plain,
    ( sK6 = k9_relat_1(sK8,k2_relat_1(sK7))
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(sK7)
    | ~ spl9_16 ),
    inference(superposition,[],[f375,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f375,plain,
    ( sK6 = k2_relat_1(k5_relat_1(sK7,sK8))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl9_16
  <=> sK6 = k2_relat_1(k5_relat_1(sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f170,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2
      | ~ r1_tarski(X2,k2_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f85,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f930,plain,
    ( spl9_13
    | ~ spl9_5
    | ~ spl9_43
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f929,f812,f533,f235,f332])).

fof(f235,plain,
    ( spl9_5
  <=> sK5 = k1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f533,plain,
    ( spl9_43
  <=> sK6 = k2_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f929,plain,
    ( sK5 = k2_relat_1(k2_funct_1(sK8))
    | ~ spl9_5
    | ~ spl9_43
    | ~ spl9_58 ),
    inference(forward_demodulation,[],[f928,f557])).

fof(f557,plain,
    ( sK5 = k10_relat_1(sK8,sK6)
    | ~ spl9_5
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f556,f237])).

fof(f237,plain,
    ( sK5 = k1_relat_1(sK8)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f235])).

fof(f556,plain,
    ( k1_relat_1(sK8) = k10_relat_1(sK8,sK6)
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f547,f112])).

fof(f547,plain,
    ( k1_relat_1(sK8) = k10_relat_1(sK8,sK6)
    | ~ v1_relat_1(sK8)
    | ~ spl9_43 ),
    inference(superposition,[],[f73,f535])).

fof(f535,plain,
    ( sK6 = k2_relat_1(sK8)
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f533])).

fof(f73,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f928,plain,
    ( k2_relat_1(k2_funct_1(sK8)) = k10_relat_1(sK8,sK6)
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f927,f112])).

fof(f927,plain,
    ( k2_relat_1(k2_funct_1(sK8)) = k10_relat_1(sK8,sK6)
    | ~ v1_relat_1(sK8)
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f926,f66])).

fof(f926,plain,
    ( k2_relat_1(k2_funct_1(sK8)) = k10_relat_1(sK8,sK6)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f917,f70])).

fof(f917,plain,
    ( k2_relat_1(k2_funct_1(sK8)) = k10_relat_1(sK8,sK6)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_58 ),
    inference(superposition,[],[f83,f814])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f823,plain,(
    spl9_54 ),
    inference(avatar_contradiction_clause,[],[f822])).

fof(f822,plain,
    ( $false
    | spl9_54 ),
    inference(subsumption_resolution,[],[f821,f112])).

fof(f821,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_54 ),
    inference(subsumption_resolution,[],[f820,f66])).

fof(f820,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_54 ),
    inference(subsumption_resolution,[],[f819,f70])).

fof(f819,plain,
    ( ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_54 ),
    inference(resolution,[],[f818,f78])).

fof(f78,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f25,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f818,plain,
    ( ~ sP0(sK8)
    | spl9_54 ),
    inference(resolution,[],[f796,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f796,plain,
    ( ~ v1_funct_1(k2_funct_1(sK8))
    | spl9_54 ),
    inference(avatar_component_clause,[],[f794])).

fof(f815,plain,
    ( ~ spl9_54
    | spl9_58
    | ~ spl9_10
    | ~ spl9_49 ),
    inference(avatar_split_clause,[],[f810,f633,f274,f812,f794])).

fof(f633,plain,
    ( spl9_49
  <=> sK6 = k1_relat_1(k2_funct_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f810,plain,
    ( k2_relat_1(k2_funct_1(sK8)) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ spl9_10
    | ~ spl9_49 ),
    inference(subsumption_resolution,[],[f784,f275])).

fof(f784,plain,
    ( k2_relat_1(k2_funct_1(sK8)) = k9_relat_1(k2_funct_1(sK8),sK6)
    | ~ v1_funct_1(k2_funct_1(sK8))
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_49 ),
    inference(superposition,[],[f182,f635])).

fof(f635,plain,
    ( sK6 = k1_relat_1(k2_funct_1(sK8))
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f633])).

fof(f182,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f181,f105])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f181,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ r1_tarski(k2_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f85,f73])).

fof(f777,plain,
    ( spl9_49
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_48 ),
    inference(avatar_split_clause,[],[f776,f629,f373,f274,f633])).

fof(f629,plain,
    ( spl9_48
  <=> r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f776,plain,
    ( sK6 = k1_relat_1(k2_funct_1(sK8))
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_48 ),
    inference(subsumption_resolution,[],[f775,f530])).

fof(f530,plain,
    ( r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8)))
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f529,f112])).

fof(f529,plain,
    ( r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8)))
    | ~ v1_relat_1(sK8)
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f528,f66])).

fof(f528,plain,
    ( r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8)))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f527,f70])).

fof(f527,plain,
    ( r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8)))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_10
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f520,f275])).

fof(f520,plain,
    ( r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8)))
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ spl9_16 ),
    inference(superposition,[],[f160,f460])).

fof(f160,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X0,X1),k1_relat_1(k2_funct_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f79,f84])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f775,plain,
    ( sK6 = k1_relat_1(k2_funct_1(sK8))
    | ~ r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8)))
    | ~ spl9_48 ),
    inference(resolution,[],[f630,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f630,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6)
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f629])).

fof(f774,plain,
    ( spl9_48
    | ~ spl9_10
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f773,f533,f274,f629])).

fof(f773,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6)
    | ~ spl9_10
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f772,f275])).

fof(f772,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6)
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f771,f112])).

fof(f771,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6)
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f770,f66])).

fof(f770,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f739,f70])).

fof(f739,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6)
    | ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | ~ v1_relat_1(k2_funct_1(sK8))
    | ~ spl9_43 ),
    inference(superposition,[],[f558,f159])).

fof(f159,plain,(
    ! [X2] :
      ( k1_relat_1(k2_funct_1(X2)) = k9_relat_1(X2,k2_relat_1(k2_funct_1(X2)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k2_funct_1(X2)) ) ),
    inference(superposition,[],[f84,f73])).

fof(f558,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK8,X0),sK6)
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f548,f112])).

fof(f548,plain,
    ( ! [X0] :
        ( r1_tarski(k9_relat_1(sK8,X0),sK6)
        | ~ v1_relat_1(sK8) )
    | ~ spl9_43 ),
    inference(superposition,[],[f80,f535])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f601,plain,
    ( spl9_15
    | ~ spl9_1 ),
    inference(avatar_split_clause,[],[f600,f139,f369])).

fof(f369,plain,
    ( spl9_15
  <=> m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f139,plain,
    ( spl9_1
  <=> m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f600,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f599,f63])).

fof(f63,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f599,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ v1_funct_1(sK7)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f598,f65])).

fof(f598,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f597,f66])).

fof(f597,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f575,f68])).

fof(f575,plain,
    ( m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ spl9_1 ),
    inference(superposition,[],[f140,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f140,plain,
    ( m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f545,plain,
    ( spl9_43
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f526,f373,f533])).

fof(f526,plain,
    ( sK6 = k2_relat_1(sK8)
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f525,f125])).

fof(f125,plain,(
    v5_relat_1(sK8,sK6) ),
    inference(resolution,[],[f93,f68])).

fof(f525,plain,
    ( ~ v5_relat_1(sK8,sK6)
    | sK6 = k2_relat_1(sK8)
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f524,f460])).

fof(f524,plain,
    ( sK6 = k2_relat_1(sK8)
    | ~ v5_relat_1(sK8,k9_relat_1(sK8,k2_relat_1(sK7)))
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f518,f112])).

fof(f518,plain,
    ( sK6 = k2_relat_1(sK8)
    | ~ v5_relat_1(sK8,k9_relat_1(sK8,k2_relat_1(sK7)))
    | ~ v1_relat_1(sK8)
    | ~ spl9_16 ),
    inference(superposition,[],[f460,f153])).

fof(f153,plain,(
    ! [X4,X3] :
      ( k2_relat_1(X3) = k9_relat_1(X3,X4)
      | ~ v5_relat_1(X3,k9_relat_1(X3,X4))
      | ~ v1_relat_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X4,X3] :
      ( k2_relat_1(X3) = k9_relat_1(X3,X4)
      | ~ v5_relat_1(X3,k9_relat_1(X3,X4))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f119,f80])).

fof(f119,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X2))
      | k2_relat_1(X2) = X1
      | ~ v5_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f88,f81])).

fof(f377,plain,
    ( ~ spl9_15
    | spl9_16 ),
    inference(avatar_split_clause,[],[f367,f373,f369])).

fof(f367,plain,
    ( sK6 = k2_relat_1(k5_relat_1(sK7,sK8))
    | ~ m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) ),
    inference(superposition,[],[f91,f306])).

fof(f306,plain,(
    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) ),
    inference(subsumption_resolution,[],[f305,f63])).

fof(f305,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f304,f65])).

fof(f304,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f303,f66])).

fof(f303,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7) ),
    inference(subsumption_resolution,[],[f296,f68])).

fof(f296,plain,
    ( sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7) ),
    inference(superposition,[],[f69,f102])).

fof(f69,plain,(
    sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f53])).

fof(f354,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f353])).

fof(f353,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f352,f63])).

fof(f352,plain,
    ( ~ v1_funct_1(sK7)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f351,f65])).

fof(f351,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f350,f66])).

fof(f350,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f341,f68])).

fof(f341,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | spl9_1 ),
    inference(resolution,[],[f104,f141])).

fof(f141,plain,
    ( ~ m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f294,plain,(
    ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f292,f71])).

fof(f71,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f53])).

fof(f292,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_6 ),
    inference(resolution,[],[f241,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f241,plain,
    ( sP1(sK5,sK6)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl9_6
  <=> sP1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f291,plain,(
    spl9_10 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | spl9_10 ),
    inference(subsumption_resolution,[],[f289,f112])).

fof(f289,plain,
    ( ~ v1_relat_1(sK8)
    | spl9_10 ),
    inference(subsumption_resolution,[],[f288,f66])).

fof(f288,plain,
    ( ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_10 ),
    inference(subsumption_resolution,[],[f287,f70])).

fof(f287,plain,
    ( ~ v2_funct_1(sK8)
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8)
    | spl9_10 ),
    inference(resolution,[],[f286,f78])).

fof(f286,plain,
    ( ~ sP0(sK8)
    | spl9_10 ),
    inference(resolution,[],[f276,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f276,plain,
    ( ~ v1_relat_1(k2_funct_1(sK8))
    | spl9_10 ),
    inference(avatar_component_clause,[],[f274])).

fof(f242,plain,
    ( spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f233,f239,f235])).

fof(f233,plain,
    ( sP1(sK5,sK6)
    | sK5 = k1_relat_1(sK8) ),
    inference(subsumption_resolution,[],[f222,f67])).

fof(f67,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f222,plain,
    ( ~ v1_funct_2(sK8,sK5,sK6)
    | sP1(sK5,sK6)
    | sK5 = k1_relat_1(sK8) ),
    inference(resolution,[],[f199,f68])).

fof(f199,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f197,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f40,f49,f48,f47])).

fof(f48,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f197,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f96,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:32:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (21293)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.54  % (21292)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.55  % (21288)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.55  % (21286)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.56  % (21285)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % (21282)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.56  % (21307)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.56  % (21290)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.57  % (21303)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.57  % (21295)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (21305)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.57  % (21304)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.57  % (21296)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.57  % (21306)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.57  % (21297)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.57  % (21299)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.58  % (21287)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.58  % (21301)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.58  % (21289)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.59  % (21283)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.59  % (21291)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.60  % (21284)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.95/0.62  % (21302)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.95/0.63  % (21294)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 2.10/0.63  % (21300)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 2.10/0.63  % (21286)Refutation found. Thanks to Tanya!
% 2.10/0.63  % SZS status Theorem for theBenchmark
% 2.10/0.63  % SZS output start Proof for theBenchmark
% 2.10/0.63  fof(f1337,plain,(
% 2.10/0.63    $false),
% 2.10/0.63    inference(avatar_sat_refutation,[],[f242,f291,f294,f354,f377,f545,f601,f774,f777,f815,f823,f930,f1336])).
% 2.10/0.63  fof(f1336,plain,(
% 2.10/0.63    ~spl9_10 | ~spl9_13 | ~spl9_16 | ~spl9_54 | ~spl9_58),
% 2.10/0.63    inference(avatar_contradiction_clause,[],[f1335])).
% 2.10/0.63  fof(f1335,plain,(
% 2.10/0.63    $false | (~spl9_10 | ~spl9_13 | ~spl9_16 | ~spl9_54 | ~spl9_58)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1334,f111])).
% 2.10/0.63  fof(f111,plain,(
% 2.10/0.63    v1_relat_1(sK7)),
% 2.10/0.63    inference(resolution,[],[f89,f65])).
% 2.10/0.63  fof(f65,plain,(
% 2.10/0.63    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 2.10/0.63    inference(cnf_transformation,[],[f53])).
% 2.10/0.63  fof(f53,plain,(
% 2.10/0.63    (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(sK8) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 2.10/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f21,f52,f51])).
% 2.10/0.63  fof(f51,plain,(
% 2.10/0.63    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(X4) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X4,sK5,sK6) & v1_funct_1(X4)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f52,plain,(
% 2.10/0.63    ? [X4] : (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(X4) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X4,sK5,sK6) & v1_funct_1(X4)) => (sK5 != k2_relset_1(sK4,sK5,sK7) & k1_xboole_0 != sK6 & v2_funct_1(sK8) & sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 2.10/0.63    introduced(choice_axiom,[])).
% 2.10/0.63  fof(f21,plain,(
% 2.10/0.63    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.10/0.63    inference(flattening,[],[f20])).
% 2.10/0.63  fof(f20,plain,(
% 2.10/0.63    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.10/0.63    inference(ennf_transformation,[],[f19])).
% 2.10/0.63  fof(f19,negated_conjecture,(
% 2.10/0.63    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 2.10/0.63    inference(negated_conjecture,[],[f18])).
% 2.10/0.63  fof(f18,conjecture,(
% 2.10/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).
% 2.10/0.63  fof(f89,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f35])).
% 2.10/0.63  fof(f35,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(ennf_transformation,[],[f11])).
% 2.10/0.63  fof(f11,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.10/0.63  fof(f1334,plain,(
% 2.10/0.63    ~v1_relat_1(sK7) | (~spl9_10 | ~spl9_13 | ~spl9_16 | ~spl9_54 | ~spl9_58)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1333,f124])).
% 2.10/0.63  fof(f124,plain,(
% 2.10/0.63    v5_relat_1(sK7,sK5)),
% 2.10/0.63    inference(resolution,[],[f93,f65])).
% 2.10/0.63  fof(f93,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f38])).
% 2.10/0.63  fof(f38,plain,(
% 2.10/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(ennf_transformation,[],[f12])).
% 2.10/0.63  fof(f12,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.10/0.63  fof(f1333,plain,(
% 2.10/0.63    ~v5_relat_1(sK7,sK5) | ~v1_relat_1(sK7) | (~spl9_10 | ~spl9_13 | ~spl9_16 | ~spl9_54 | ~spl9_58)),
% 2.10/0.63    inference(resolution,[],[f1211,f81])).
% 2.10/0.63  fof(f81,plain,(
% 2.10/0.63    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f55])).
% 2.10/0.63  fof(f55,plain,(
% 2.10/0.63    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.10/0.63    inference(nnf_transformation,[],[f28])).
% 2.10/0.63  fof(f28,plain,(
% 2.10/0.63    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.10/0.63    inference(ennf_transformation,[],[f2])).
% 2.10/0.63  fof(f2,axiom,(
% 2.10/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.10/0.63  fof(f1211,plain,(
% 2.10/0.63    ~r1_tarski(k2_relat_1(sK7),sK5) | (~spl9_10 | ~spl9_13 | ~spl9_16 | ~spl9_54 | ~spl9_58)),
% 2.10/0.63    inference(forward_demodulation,[],[f1210,f334])).
% 2.10/0.63  fof(f334,plain,(
% 2.10/0.63    sK5 = k2_relat_1(k2_funct_1(sK8)) | ~spl9_13),
% 2.10/0.63    inference(avatar_component_clause,[],[f332])).
% 2.10/0.63  fof(f332,plain,(
% 2.10/0.63    spl9_13 <=> sK5 = k2_relat_1(k2_funct_1(sK8))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 2.10/0.63  fof(f1210,plain,(
% 2.10/0.63    ~r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8))) | (~spl9_10 | ~spl9_13 | ~spl9_16 | ~spl9_54 | ~spl9_58)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1209,f147])).
% 2.10/0.63  fof(f147,plain,(
% 2.10/0.63    sK5 != k2_relat_1(sK7)),
% 2.10/0.63    inference(subsumption_resolution,[],[f136,f65])).
% 2.10/0.63  fof(f136,plain,(
% 2.10/0.63    sK5 != k2_relat_1(sK7) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 2.10/0.63    inference(superposition,[],[f72,f91])).
% 2.10/0.63  fof(f91,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f37])).
% 2.10/0.63  fof(f37,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(ennf_transformation,[],[f14])).
% 2.10/0.63  fof(f14,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.10/0.63  fof(f72,plain,(
% 2.10/0.63    sK5 != k2_relset_1(sK4,sK5,sK7)),
% 2.10/0.63    inference(cnf_transformation,[],[f53])).
% 2.10/0.63  fof(f1209,plain,(
% 2.10/0.63    sK5 = k2_relat_1(sK7) | ~r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8))) | (~spl9_10 | ~spl9_13 | ~spl9_16 | ~spl9_54 | ~spl9_58)),
% 2.10/0.63    inference(forward_demodulation,[],[f1208,f931])).
% 2.10/0.63  fof(f931,plain,(
% 2.10/0.63    sK5 = k9_relat_1(k2_funct_1(sK8),sK6) | (~spl9_13 | ~spl9_58)),
% 2.10/0.63    inference(backward_demodulation,[],[f814,f334])).
% 2.10/0.63  fof(f814,plain,(
% 2.10/0.63    k2_relat_1(k2_funct_1(sK8)) = k9_relat_1(k2_funct_1(sK8),sK6) | ~spl9_58),
% 2.10/0.63    inference(avatar_component_clause,[],[f812])).
% 2.10/0.63  fof(f812,plain,(
% 2.10/0.63    spl9_58 <=> k2_relat_1(k2_funct_1(sK8)) = k9_relat_1(k2_funct_1(sK8),sK6)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).
% 2.10/0.63  fof(f1208,plain,(
% 2.10/0.63    k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6) | ~r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8))) | (~spl9_10 | ~spl9_16 | ~spl9_54)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1207,f112])).
% 2.10/0.63  fof(f112,plain,(
% 2.10/0.63    v1_relat_1(sK8)),
% 2.10/0.63    inference(resolution,[],[f89,f68])).
% 2.10/0.63  fof(f68,plain,(
% 2.10/0.63    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 2.10/0.63    inference(cnf_transformation,[],[f53])).
% 2.10/0.63  fof(f1207,plain,(
% 2.10/0.63    k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6) | ~r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8))) | ~v1_relat_1(sK8) | (~spl9_10 | ~spl9_16 | ~spl9_54)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1206,f66])).
% 2.10/0.63  fof(f66,plain,(
% 2.10/0.63    v1_funct_1(sK8)),
% 2.10/0.63    inference(cnf_transformation,[],[f53])).
% 2.10/0.63  fof(f1206,plain,(
% 2.10/0.63    k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6) | ~r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8))) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_10 | ~spl9_16 | ~spl9_54)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1205,f70])).
% 2.10/0.63  fof(f70,plain,(
% 2.10/0.63    v2_funct_1(sK8)),
% 2.10/0.63    inference(cnf_transformation,[],[f53])).
% 2.10/0.63  fof(f1205,plain,(
% 2.10/0.63    k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6) | ~r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8))) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_10 | ~spl9_16 | ~spl9_54)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1204,f275])).
% 2.10/0.63  fof(f275,plain,(
% 2.10/0.63    v1_relat_1(k2_funct_1(sK8)) | ~spl9_10),
% 2.10/0.63    inference(avatar_component_clause,[],[f274])).
% 2.10/0.63  fof(f274,plain,(
% 2.10/0.63    spl9_10 <=> v1_relat_1(k2_funct_1(sK8))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 2.10/0.63  fof(f1204,plain,(
% 2.10/0.63    k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6) | ~r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8))) | ~v1_relat_1(k2_funct_1(sK8)) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_16 | ~spl9_54)),
% 2.10/0.63    inference(subsumption_resolution,[],[f1176,f795])).
% 2.10/0.63  fof(f795,plain,(
% 2.10/0.63    v1_funct_1(k2_funct_1(sK8)) | ~spl9_54),
% 2.10/0.63    inference(avatar_component_clause,[],[f794])).
% 2.10/0.63  fof(f794,plain,(
% 2.10/0.63    spl9_54 <=> v1_funct_1(k2_funct_1(sK8))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 2.10/0.63  fof(f1176,plain,(
% 2.10/0.63    k2_relat_1(sK7) = k9_relat_1(k2_funct_1(sK8),sK6) | ~r1_tarski(k2_relat_1(sK7),k2_relat_1(k2_funct_1(sK8))) | ~v1_funct_1(k2_funct_1(sK8)) | ~v1_relat_1(k2_funct_1(sK8)) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_16),
% 2.10/0.63    inference(superposition,[],[f170,f460])).
% 2.10/0.63  fof(f460,plain,(
% 2.10/0.63    sK6 = k9_relat_1(sK8,k2_relat_1(sK7)) | ~spl9_16),
% 2.10/0.63    inference(subsumption_resolution,[],[f459,f111])).
% 2.10/0.63  fof(f459,plain,(
% 2.10/0.63    sK6 = k9_relat_1(sK8,k2_relat_1(sK7)) | ~v1_relat_1(sK7) | ~spl9_16),
% 2.10/0.63    inference(subsumption_resolution,[],[f448,f112])).
% 2.10/0.63  fof(f448,plain,(
% 2.10/0.63    sK6 = k9_relat_1(sK8,k2_relat_1(sK7)) | ~v1_relat_1(sK8) | ~v1_relat_1(sK7) | ~spl9_16),
% 2.10/0.63    inference(superposition,[],[f375,f74])).
% 2.10/0.63  fof(f74,plain,(
% 2.10/0.63    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f23])).
% 2.10/0.63  fof(f23,plain,(
% 2.10/0.63    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f4])).
% 2.10/0.63  fof(f4,axiom,(
% 2.10/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 2.10/0.63  fof(f375,plain,(
% 2.10/0.63    sK6 = k2_relat_1(k5_relat_1(sK7,sK8)) | ~spl9_16),
% 2.10/0.63    inference(avatar_component_clause,[],[f373])).
% 2.10/0.63  fof(f373,plain,(
% 2.10/0.63    spl9_16 <=> sK6 = k2_relat_1(k5_relat_1(sK7,sK8))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 2.10/0.63  fof(f170,plain,(
% 2.10/0.63    ( ! [X2,X1] : (k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X2)) = X2 | ~r1_tarski(X2,k2_relat_1(k2_funct_1(X1))) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.10/0.63    inference(superposition,[],[f85,f84])).
% 2.10/0.63  fof(f84,plain,(
% 2.10/0.63    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f32])).
% 2.10/0.63  fof(f32,plain,(
% 2.10/0.63    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.10/0.63    inference(flattening,[],[f31])).
% 2.10/0.63  fof(f31,plain,(
% 2.10/0.63    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.10/0.63    inference(ennf_transformation,[],[f9])).
% 2.10/0.63  fof(f9,axiom,(
% 2.10/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).
% 2.10/0.63  fof(f85,plain,(
% 2.10/0.63    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f34])).
% 2.10/0.63  fof(f34,plain,(
% 2.10/0.63    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.10/0.63    inference(flattening,[],[f33])).
% 2.10/0.63  fof(f33,plain,(
% 2.10/0.63    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.10/0.63    inference(ennf_transformation,[],[f8])).
% 2.10/0.63  fof(f8,axiom,(
% 2.10/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 2.10/0.63  fof(f930,plain,(
% 2.10/0.63    spl9_13 | ~spl9_5 | ~spl9_43 | ~spl9_58),
% 2.10/0.63    inference(avatar_split_clause,[],[f929,f812,f533,f235,f332])).
% 2.10/0.63  fof(f235,plain,(
% 2.10/0.63    spl9_5 <=> sK5 = k1_relat_1(sK8)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 2.10/0.63  fof(f533,plain,(
% 2.10/0.63    spl9_43 <=> sK6 = k2_relat_1(sK8)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 2.10/0.63  fof(f929,plain,(
% 2.10/0.63    sK5 = k2_relat_1(k2_funct_1(sK8)) | (~spl9_5 | ~spl9_43 | ~spl9_58)),
% 2.10/0.63    inference(forward_demodulation,[],[f928,f557])).
% 2.10/0.63  fof(f557,plain,(
% 2.10/0.63    sK5 = k10_relat_1(sK8,sK6) | (~spl9_5 | ~spl9_43)),
% 2.10/0.63    inference(forward_demodulation,[],[f556,f237])).
% 2.10/0.63  fof(f237,plain,(
% 2.10/0.63    sK5 = k1_relat_1(sK8) | ~spl9_5),
% 2.10/0.63    inference(avatar_component_clause,[],[f235])).
% 2.10/0.63  fof(f556,plain,(
% 2.10/0.63    k1_relat_1(sK8) = k10_relat_1(sK8,sK6) | ~spl9_43),
% 2.10/0.63    inference(subsumption_resolution,[],[f547,f112])).
% 2.10/0.63  fof(f547,plain,(
% 2.10/0.63    k1_relat_1(sK8) = k10_relat_1(sK8,sK6) | ~v1_relat_1(sK8) | ~spl9_43),
% 2.10/0.63    inference(superposition,[],[f73,f535])).
% 2.10/0.63  fof(f535,plain,(
% 2.10/0.63    sK6 = k2_relat_1(sK8) | ~spl9_43),
% 2.10/0.63    inference(avatar_component_clause,[],[f533])).
% 2.10/0.63  fof(f73,plain,(
% 2.10/0.63    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f22])).
% 2.10/0.63  fof(f22,plain,(
% 2.10/0.63    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.10/0.63    inference(ennf_transformation,[],[f6])).
% 2.10/0.63  fof(f6,axiom,(
% 2.10/0.63    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.10/0.63  fof(f928,plain,(
% 2.10/0.63    k2_relat_1(k2_funct_1(sK8)) = k10_relat_1(sK8,sK6) | ~spl9_58),
% 2.10/0.63    inference(subsumption_resolution,[],[f927,f112])).
% 2.10/0.63  fof(f927,plain,(
% 2.10/0.63    k2_relat_1(k2_funct_1(sK8)) = k10_relat_1(sK8,sK6) | ~v1_relat_1(sK8) | ~spl9_58),
% 2.10/0.63    inference(subsumption_resolution,[],[f926,f66])).
% 2.10/0.63  fof(f926,plain,(
% 2.10/0.63    k2_relat_1(k2_funct_1(sK8)) = k10_relat_1(sK8,sK6) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_58),
% 2.10/0.63    inference(subsumption_resolution,[],[f917,f70])).
% 2.10/0.63  fof(f917,plain,(
% 2.10/0.63    k2_relat_1(k2_funct_1(sK8)) = k10_relat_1(sK8,sK6) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_58),
% 2.10/0.63    inference(superposition,[],[f83,f814])).
% 2.10/0.63  fof(f83,plain,(
% 2.10/0.63    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f30])).
% 2.10/0.63  fof(f30,plain,(
% 2.10/0.63    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.10/0.63    inference(flattening,[],[f29])).
% 2.10/0.63  fof(f29,plain,(
% 2.10/0.63    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.10/0.63    inference(ennf_transformation,[],[f10])).
% 2.10/0.63  fof(f10,axiom,(
% 2.10/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 2.10/0.63  fof(f823,plain,(
% 2.10/0.63    spl9_54),
% 2.10/0.63    inference(avatar_contradiction_clause,[],[f822])).
% 2.10/0.63  fof(f822,plain,(
% 2.10/0.63    $false | spl9_54),
% 2.10/0.63    inference(subsumption_resolution,[],[f821,f112])).
% 2.10/0.63  fof(f821,plain,(
% 2.10/0.63    ~v1_relat_1(sK8) | spl9_54),
% 2.10/0.63    inference(subsumption_resolution,[],[f820,f66])).
% 2.10/0.63  fof(f820,plain,(
% 2.10/0.63    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_54),
% 2.10/0.63    inference(subsumption_resolution,[],[f819,f70])).
% 2.10/0.63  fof(f819,plain,(
% 2.10/0.63    ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_54),
% 2.10/0.63    inference(resolution,[],[f818,f78])).
% 2.10/0.63  fof(f78,plain,(
% 2.10/0.63    ( ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f46])).
% 2.10/0.63  fof(f46,plain,(
% 2.10/0.63    ! [X0] : (sP0(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.10/0.63    inference(definition_folding,[],[f25,f45])).
% 2.10/0.63  fof(f45,plain,(
% 2.10/0.63    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 2.10/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.10/0.63  fof(f25,plain,(
% 2.10/0.63    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.10/0.63    inference(flattening,[],[f24])).
% 2.10/0.63  fof(f24,plain,(
% 2.10/0.63    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.10/0.63    inference(ennf_transformation,[],[f7])).
% 2.10/0.63  fof(f7,axiom,(
% 2.10/0.63    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 2.10/0.63  fof(f818,plain,(
% 2.10/0.63    ~sP0(sK8) | spl9_54),
% 2.10/0.63    inference(resolution,[],[f796,f76])).
% 2.10/0.63  fof(f76,plain,(
% 2.10/0.63    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f54])).
% 2.10/0.63  fof(f54,plain,(
% 2.10/0.63    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~sP0(X0))),
% 2.10/0.63    inference(nnf_transformation,[],[f45])).
% 2.10/0.63  fof(f796,plain,(
% 2.10/0.63    ~v1_funct_1(k2_funct_1(sK8)) | spl9_54),
% 2.10/0.63    inference(avatar_component_clause,[],[f794])).
% 2.10/0.63  fof(f815,plain,(
% 2.10/0.63    ~spl9_54 | spl9_58 | ~spl9_10 | ~spl9_49),
% 2.10/0.63    inference(avatar_split_clause,[],[f810,f633,f274,f812,f794])).
% 2.10/0.63  fof(f633,plain,(
% 2.10/0.63    spl9_49 <=> sK6 = k1_relat_1(k2_funct_1(sK8))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 2.10/0.63  fof(f810,plain,(
% 2.10/0.63    k2_relat_1(k2_funct_1(sK8)) = k9_relat_1(k2_funct_1(sK8),sK6) | ~v1_funct_1(k2_funct_1(sK8)) | (~spl9_10 | ~spl9_49)),
% 2.10/0.63    inference(subsumption_resolution,[],[f784,f275])).
% 2.10/0.63  fof(f784,plain,(
% 2.10/0.63    k2_relat_1(k2_funct_1(sK8)) = k9_relat_1(k2_funct_1(sK8),sK6) | ~v1_funct_1(k2_funct_1(sK8)) | ~v1_relat_1(k2_funct_1(sK8)) | ~spl9_49),
% 2.10/0.63    inference(superposition,[],[f182,f635])).
% 2.10/0.63  fof(f635,plain,(
% 2.10/0.63    sK6 = k1_relat_1(k2_funct_1(sK8)) | ~spl9_49),
% 2.10/0.63    inference(avatar_component_clause,[],[f633])).
% 2.10/0.63  fof(f182,plain,(
% 2.10/0.63    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/0.63    inference(subsumption_resolution,[],[f181,f105])).
% 2.10/0.63  fof(f105,plain,(
% 2.10/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.10/0.63    inference(equality_resolution,[],[f87])).
% 2.10/0.63  fof(f87,plain,(
% 2.10/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.10/0.63    inference(cnf_transformation,[],[f57])).
% 2.10/0.63  fof(f57,plain,(
% 2.10/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.10/0.63    inference(flattening,[],[f56])).
% 2.10/0.63  fof(f56,plain,(
% 2.10/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.10/0.63    inference(nnf_transformation,[],[f1])).
% 2.10/0.63  fof(f1,axiom,(
% 2.10/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.10/0.63  fof(f181,plain,(
% 2.10/0.63    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/0.63    inference(duplicate_literal_removal,[],[f169])).
% 2.10/0.63  fof(f169,plain,(
% 2.10/0.63    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~r1_tarski(k2_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/0.63    inference(superposition,[],[f85,f73])).
% 2.10/0.63  fof(f777,plain,(
% 2.10/0.63    spl9_49 | ~spl9_10 | ~spl9_16 | ~spl9_48),
% 2.10/0.63    inference(avatar_split_clause,[],[f776,f629,f373,f274,f633])).
% 2.10/0.63  fof(f629,plain,(
% 2.10/0.63    spl9_48 <=> r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 2.10/0.63  fof(f776,plain,(
% 2.10/0.63    sK6 = k1_relat_1(k2_funct_1(sK8)) | (~spl9_10 | ~spl9_16 | ~spl9_48)),
% 2.10/0.63    inference(subsumption_resolution,[],[f775,f530])).
% 2.10/0.63  fof(f530,plain,(
% 2.10/0.63    r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8))) | (~spl9_10 | ~spl9_16)),
% 2.10/0.63    inference(subsumption_resolution,[],[f529,f112])).
% 2.10/0.63  fof(f529,plain,(
% 2.10/0.63    r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8))) | ~v1_relat_1(sK8) | (~spl9_10 | ~spl9_16)),
% 2.10/0.63    inference(subsumption_resolution,[],[f528,f66])).
% 2.10/0.63  fof(f528,plain,(
% 2.10/0.63    r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8))) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_10 | ~spl9_16)),
% 2.10/0.63    inference(subsumption_resolution,[],[f527,f70])).
% 2.10/0.63  fof(f527,plain,(
% 2.10/0.63    r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8))) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | (~spl9_10 | ~spl9_16)),
% 2.10/0.63    inference(subsumption_resolution,[],[f520,f275])).
% 2.10/0.63  fof(f520,plain,(
% 2.10/0.63    r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8))) | ~v1_relat_1(k2_funct_1(sK8)) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~spl9_16),
% 2.10/0.63    inference(superposition,[],[f160,f460])).
% 2.10/0.63  fof(f160,plain,(
% 2.10/0.63    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X0,X1),k1_relat_1(k2_funct_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/0.63    inference(superposition,[],[f79,f84])).
% 2.10/0.63  fof(f79,plain,(
% 2.10/0.63    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f26])).
% 2.10/0.63  fof(f26,plain,(
% 2.10/0.63    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.10/0.63    inference(ennf_transformation,[],[f5])).
% 2.10/0.63  fof(f5,axiom,(
% 2.10/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 2.10/0.63  fof(f775,plain,(
% 2.10/0.63    sK6 = k1_relat_1(k2_funct_1(sK8)) | ~r1_tarski(sK6,k1_relat_1(k2_funct_1(sK8))) | ~spl9_48),
% 2.10/0.63    inference(resolution,[],[f630,f88])).
% 2.10/0.63  fof(f88,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f57])).
% 2.10/0.63  fof(f630,plain,(
% 2.10/0.63    r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6) | ~spl9_48),
% 2.10/0.63    inference(avatar_component_clause,[],[f629])).
% 2.10/0.63  fof(f774,plain,(
% 2.10/0.63    spl9_48 | ~spl9_10 | ~spl9_43),
% 2.10/0.63    inference(avatar_split_clause,[],[f773,f533,f274,f629])).
% 2.10/0.63  fof(f773,plain,(
% 2.10/0.63    r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6) | (~spl9_10 | ~spl9_43)),
% 2.10/0.63    inference(subsumption_resolution,[],[f772,f275])).
% 2.10/0.63  fof(f772,plain,(
% 2.10/0.63    r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6) | ~v1_relat_1(k2_funct_1(sK8)) | ~spl9_43),
% 2.10/0.63    inference(subsumption_resolution,[],[f771,f112])).
% 2.10/0.63  fof(f771,plain,(
% 2.10/0.63    r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6) | ~v1_relat_1(sK8) | ~v1_relat_1(k2_funct_1(sK8)) | ~spl9_43),
% 2.10/0.63    inference(subsumption_resolution,[],[f770,f66])).
% 2.10/0.63  fof(f770,plain,(
% 2.10/0.63    r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~v1_relat_1(k2_funct_1(sK8)) | ~spl9_43),
% 2.10/0.63    inference(subsumption_resolution,[],[f739,f70])).
% 2.10/0.63  fof(f739,plain,(
% 2.10/0.63    r1_tarski(k1_relat_1(k2_funct_1(sK8)),sK6) | ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | ~v1_relat_1(k2_funct_1(sK8)) | ~spl9_43),
% 2.10/0.63    inference(superposition,[],[f558,f159])).
% 2.10/0.63  fof(f159,plain,(
% 2.10/0.63    ( ! [X2] : (k1_relat_1(k2_funct_1(X2)) = k9_relat_1(X2,k2_relat_1(k2_funct_1(X2))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k2_funct_1(X2))) )),
% 2.10/0.63    inference(superposition,[],[f84,f73])).
% 2.10/0.63  fof(f558,plain,(
% 2.10/0.63    ( ! [X0] : (r1_tarski(k9_relat_1(sK8,X0),sK6)) ) | ~spl9_43),
% 2.10/0.63    inference(subsumption_resolution,[],[f548,f112])).
% 2.10/0.63  fof(f548,plain,(
% 2.10/0.63    ( ! [X0] : (r1_tarski(k9_relat_1(sK8,X0),sK6) | ~v1_relat_1(sK8)) ) | ~spl9_43),
% 2.10/0.63    inference(superposition,[],[f80,f535])).
% 2.10/0.63  fof(f80,plain,(
% 2.10/0.63    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f27])).
% 2.10/0.63  fof(f27,plain,(
% 2.10/0.63    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.10/0.63    inference(ennf_transformation,[],[f3])).
% 2.10/0.63  fof(f3,axiom,(
% 2.10/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 2.10/0.63  fof(f601,plain,(
% 2.10/0.63    spl9_15 | ~spl9_1),
% 2.10/0.63    inference(avatar_split_clause,[],[f600,f139,f369])).
% 2.10/0.63  fof(f369,plain,(
% 2.10/0.63    spl9_15 <=> m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 2.10/0.63  fof(f139,plain,(
% 2.10/0.63    spl9_1 <=> m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.10/0.63  fof(f600,plain,(
% 2.10/0.63    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~spl9_1),
% 2.10/0.63    inference(subsumption_resolution,[],[f599,f63])).
% 2.10/0.63  fof(f63,plain,(
% 2.10/0.63    v1_funct_1(sK7)),
% 2.10/0.63    inference(cnf_transformation,[],[f53])).
% 2.10/0.63  fof(f599,plain,(
% 2.10/0.63    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~v1_funct_1(sK7) | ~spl9_1),
% 2.10/0.63    inference(subsumption_resolution,[],[f598,f65])).
% 2.10/0.63  fof(f598,plain,(
% 2.10/0.63    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~spl9_1),
% 2.10/0.63    inference(subsumption_resolution,[],[f597,f66])).
% 2.10/0.63  fof(f597,plain,(
% 2.10/0.63    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~spl9_1),
% 2.10/0.63    inference(subsumption_resolution,[],[f575,f68])).
% 2.10/0.63  fof(f575,plain,(
% 2.10/0.63    m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~spl9_1),
% 2.10/0.63    inference(superposition,[],[f140,f102])).
% 2.10/0.63  fof(f102,plain,(
% 2.10/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f42])).
% 2.10/0.63  fof(f42,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.10/0.63    inference(flattening,[],[f41])).
% 2.10/0.63  fof(f41,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.10/0.63    inference(ennf_transformation,[],[f17])).
% 2.10/0.63  fof(f17,axiom,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.10/0.63  fof(f140,plain,(
% 2.10/0.63    m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | ~spl9_1),
% 2.10/0.63    inference(avatar_component_clause,[],[f139])).
% 2.10/0.63  fof(f545,plain,(
% 2.10/0.63    spl9_43 | ~spl9_16),
% 2.10/0.63    inference(avatar_split_clause,[],[f526,f373,f533])).
% 2.10/0.63  fof(f526,plain,(
% 2.10/0.63    sK6 = k2_relat_1(sK8) | ~spl9_16),
% 2.10/0.63    inference(subsumption_resolution,[],[f525,f125])).
% 2.10/0.63  fof(f125,plain,(
% 2.10/0.63    v5_relat_1(sK8,sK6)),
% 2.10/0.63    inference(resolution,[],[f93,f68])).
% 2.10/0.63  fof(f525,plain,(
% 2.10/0.63    ~v5_relat_1(sK8,sK6) | sK6 = k2_relat_1(sK8) | ~spl9_16),
% 2.10/0.63    inference(forward_demodulation,[],[f524,f460])).
% 2.10/0.63  fof(f524,plain,(
% 2.10/0.63    sK6 = k2_relat_1(sK8) | ~v5_relat_1(sK8,k9_relat_1(sK8,k2_relat_1(sK7))) | ~spl9_16),
% 2.10/0.63    inference(subsumption_resolution,[],[f518,f112])).
% 2.10/0.63  fof(f518,plain,(
% 2.10/0.63    sK6 = k2_relat_1(sK8) | ~v5_relat_1(sK8,k9_relat_1(sK8,k2_relat_1(sK7))) | ~v1_relat_1(sK8) | ~spl9_16),
% 2.10/0.63    inference(superposition,[],[f460,f153])).
% 2.10/0.63  fof(f153,plain,(
% 2.10/0.63    ( ! [X4,X3] : (k2_relat_1(X3) = k9_relat_1(X3,X4) | ~v5_relat_1(X3,k9_relat_1(X3,X4)) | ~v1_relat_1(X3)) )),
% 2.10/0.63    inference(duplicate_literal_removal,[],[f151])).
% 2.10/0.63  fof(f151,plain,(
% 2.10/0.63    ( ! [X4,X3] : (k2_relat_1(X3) = k9_relat_1(X3,X4) | ~v5_relat_1(X3,k9_relat_1(X3,X4)) | ~v1_relat_1(X3) | ~v1_relat_1(X3)) )),
% 2.10/0.63    inference(resolution,[],[f119,f80])).
% 2.10/0.63  fof(f119,plain,(
% 2.10/0.63    ( ! [X2,X1] : (~r1_tarski(X1,k2_relat_1(X2)) | k2_relat_1(X2) = X1 | ~v5_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 2.10/0.63    inference(resolution,[],[f88,f81])).
% 2.10/0.63  fof(f377,plain,(
% 2.10/0.63    ~spl9_15 | spl9_16),
% 2.10/0.63    inference(avatar_split_clause,[],[f367,f373,f369])).
% 2.10/0.63  fof(f367,plain,(
% 2.10/0.63    sK6 = k2_relat_1(k5_relat_1(sK7,sK8)) | ~m1_subset_1(k5_relat_1(sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6)))),
% 2.10/0.63    inference(superposition,[],[f91,f306])).
% 2.10/0.63  fof(f306,plain,(
% 2.10/0.63    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8))),
% 2.10/0.63    inference(subsumption_resolution,[],[f305,f63])).
% 2.10/0.63  fof(f305,plain,(
% 2.10/0.63    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~v1_funct_1(sK7)),
% 2.10/0.63    inference(subsumption_resolution,[],[f304,f65])).
% 2.10/0.63  fof(f304,plain,(
% 2.10/0.63    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)),
% 2.10/0.63    inference(subsumption_resolution,[],[f303,f66])).
% 2.10/0.63  fof(f303,plain,(
% 2.10/0.63    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)),
% 2.10/0.63    inference(subsumption_resolution,[],[f296,f68])).
% 2.10/0.63  fof(f296,plain,(
% 2.10/0.63    sK6 = k2_relset_1(sK4,sK6,k5_relat_1(sK7,sK8)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7)),
% 2.10/0.63    inference(superposition,[],[f69,f102])).
% 2.10/0.63  fof(f69,plain,(
% 2.10/0.63    sK6 = k2_relset_1(sK4,sK6,k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8))),
% 2.10/0.63    inference(cnf_transformation,[],[f53])).
% 2.10/0.63  fof(f354,plain,(
% 2.10/0.63    spl9_1),
% 2.10/0.63    inference(avatar_contradiction_clause,[],[f353])).
% 2.10/0.63  fof(f353,plain,(
% 2.10/0.63    $false | spl9_1),
% 2.10/0.63    inference(subsumption_resolution,[],[f352,f63])).
% 2.10/0.63  fof(f352,plain,(
% 2.10/0.63    ~v1_funct_1(sK7) | spl9_1),
% 2.10/0.63    inference(subsumption_resolution,[],[f351,f65])).
% 2.10/0.63  fof(f351,plain,(
% 2.10/0.63    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | spl9_1),
% 2.10/0.63    inference(subsumption_resolution,[],[f350,f66])).
% 2.10/0.63  fof(f350,plain,(
% 2.10/0.63    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | spl9_1),
% 2.10/0.63    inference(subsumption_resolution,[],[f341,f68])).
% 2.10/0.63  fof(f341,plain,(
% 2.10/0.63    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | spl9_1),
% 2.10/0.63    inference(resolution,[],[f104,f141])).
% 2.10/0.63  fof(f141,plain,(
% 2.10/0.63    ~m1_subset_1(k1_partfun1(sK4,sK5,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(sK4,sK6))) | spl9_1),
% 2.10/0.63    inference(avatar_component_clause,[],[f139])).
% 2.10/0.63  fof(f104,plain,(
% 2.10/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f44])).
% 2.10/0.63  fof(f44,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.10/0.63    inference(flattening,[],[f43])).
% 2.10/0.63  fof(f43,plain,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.10/0.63    inference(ennf_transformation,[],[f16])).
% 2.10/0.63  fof(f16,axiom,(
% 2.10/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.10/0.63  fof(f294,plain,(
% 2.10/0.63    ~spl9_6),
% 2.10/0.63    inference(avatar_contradiction_clause,[],[f293])).
% 2.10/0.63  fof(f293,plain,(
% 2.10/0.63    $false | ~spl9_6),
% 2.10/0.63    inference(subsumption_resolution,[],[f292,f71])).
% 2.10/0.63  fof(f71,plain,(
% 2.10/0.63    k1_xboole_0 != sK6),
% 2.10/0.63    inference(cnf_transformation,[],[f53])).
% 2.10/0.63  fof(f292,plain,(
% 2.10/0.63    k1_xboole_0 = sK6 | ~spl9_6),
% 2.10/0.63    inference(resolution,[],[f241,f98])).
% 2.10/0.63  fof(f98,plain,(
% 2.10/0.63    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 2.10/0.63    inference(cnf_transformation,[],[f62])).
% 2.10/0.63  fof(f62,plain,(
% 2.10/0.63    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 2.10/0.63    inference(nnf_transformation,[],[f47])).
% 2.10/0.63  fof(f47,plain,(
% 2.10/0.63    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 2.10/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.10/0.63  fof(f241,plain,(
% 2.10/0.63    sP1(sK5,sK6) | ~spl9_6),
% 2.10/0.63    inference(avatar_component_clause,[],[f239])).
% 2.10/0.63  fof(f239,plain,(
% 2.10/0.63    spl9_6 <=> sP1(sK5,sK6)),
% 2.10/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 2.10/0.63  fof(f291,plain,(
% 2.10/0.63    spl9_10),
% 2.10/0.63    inference(avatar_contradiction_clause,[],[f290])).
% 2.10/0.63  fof(f290,plain,(
% 2.10/0.63    $false | spl9_10),
% 2.10/0.63    inference(subsumption_resolution,[],[f289,f112])).
% 2.10/0.63  fof(f289,plain,(
% 2.10/0.63    ~v1_relat_1(sK8) | spl9_10),
% 2.10/0.63    inference(subsumption_resolution,[],[f288,f66])).
% 2.10/0.63  fof(f288,plain,(
% 2.10/0.63    ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_10),
% 2.10/0.63    inference(subsumption_resolution,[],[f287,f70])).
% 2.10/0.63  fof(f287,plain,(
% 2.10/0.63    ~v2_funct_1(sK8) | ~v1_funct_1(sK8) | ~v1_relat_1(sK8) | spl9_10),
% 2.10/0.63    inference(resolution,[],[f286,f78])).
% 2.10/0.63  fof(f286,plain,(
% 2.10/0.63    ~sP0(sK8) | spl9_10),
% 2.10/0.63    inference(resolution,[],[f276,f75])).
% 2.10/0.63  fof(f75,plain,(
% 2.10/0.63    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~sP0(X0)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f54])).
% 2.10/0.63  fof(f276,plain,(
% 2.10/0.63    ~v1_relat_1(k2_funct_1(sK8)) | spl9_10),
% 2.10/0.63    inference(avatar_component_clause,[],[f274])).
% 2.10/0.63  fof(f242,plain,(
% 2.10/0.63    spl9_5 | spl9_6),
% 2.10/0.63    inference(avatar_split_clause,[],[f233,f239,f235])).
% 2.10/0.63  fof(f233,plain,(
% 2.10/0.63    sP1(sK5,sK6) | sK5 = k1_relat_1(sK8)),
% 2.10/0.63    inference(subsumption_resolution,[],[f222,f67])).
% 2.10/0.63  fof(f67,plain,(
% 2.10/0.63    v1_funct_2(sK8,sK5,sK6)),
% 2.10/0.63    inference(cnf_transformation,[],[f53])).
% 2.10/0.63  fof(f222,plain,(
% 2.10/0.63    ~v1_funct_2(sK8,sK5,sK6) | sP1(sK5,sK6) | sK5 = k1_relat_1(sK8)),
% 2.10/0.63    inference(resolution,[],[f199,f68])).
% 2.10/0.63  fof(f199,plain,(
% 2.10/0.63    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 2.10/0.63    inference(subsumption_resolution,[],[f197,f100])).
% 2.10/0.63  fof(f100,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f50])).
% 2.10/0.63  fof(f50,plain,(
% 2.10/0.63    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(definition_folding,[],[f40,f49,f48,f47])).
% 2.10/0.63  fof(f48,plain,(
% 2.10/0.63    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 2.10/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.10/0.63  fof(f49,plain,(
% 2.10/0.63    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 2.10/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.10/0.63  fof(f40,plain,(
% 2.10/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(flattening,[],[f39])).
% 2.10/0.63  fof(f39,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(ennf_transformation,[],[f15])).
% 2.10/0.63  fof(f15,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.10/0.63  fof(f197,plain,(
% 2.10/0.63    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.10/0.63    inference(superposition,[],[f96,f90])).
% 2.10/0.63  fof(f90,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/0.63    inference(cnf_transformation,[],[f36])).
% 2.10/0.63  fof(f36,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/0.63    inference(ennf_transformation,[],[f13])).
% 2.10/0.63  fof(f13,axiom,(
% 2.10/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.10/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.10/0.63  fof(f96,plain,(
% 2.10/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 2.10/0.63    inference(cnf_transformation,[],[f61])).
% 2.10/0.63  fof(f61,plain,(
% 2.10/0.63    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 2.10/0.63    inference(rectify,[],[f60])).
% 2.10/0.63  fof(f60,plain,(
% 2.10/0.63    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 2.10/0.63    inference(nnf_transformation,[],[f48])).
% 2.10/0.63  % SZS output end Proof for theBenchmark
% 2.10/0.63  % (21286)------------------------------
% 2.10/0.63  % (21286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.63  % (21286)Termination reason: Refutation
% 2.10/0.63  
% 2.10/0.63  % (21286)Memory used [KB]: 6780
% 2.10/0.63  % (21286)Time elapsed: 0.174 s
% 2.10/0.63  % (21286)------------------------------
% 2.10/0.63  % (21286)------------------------------
% 2.10/0.63  % (21281)Success in time 0.266 s
%------------------------------------------------------------------------------
