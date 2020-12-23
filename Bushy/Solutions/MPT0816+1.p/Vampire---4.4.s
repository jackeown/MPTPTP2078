%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t11_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:07 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 477 expanded)
%              Number of leaves         :   49 ( 179 expanded)
%              Depth                    :   11
%              Number of atoms          :  431 (1190 expanded)
%              Number of equality atoms :   16 (  38 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f452,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f80,f87,f94,f101,f108,f119,f145,f159,f172,f181,f197,f210,f232,f239,f253,f265,f273,f322,f335,f346,f356,f382,f398,f451])).

fof(f451,plain,
    ( ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f450])).

fof(f450,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f449,f93])).

fof(f93,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_6
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f449,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f446,f100])).

fof(f100,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_8
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f446,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl4_0
    | ~ spl4_13 ),
    inference(resolution,[],[f444,f118])).

fof(f118,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_13
  <=> ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f444,plain,
    ( ! [X0,X1] :
        ( r1_tarski(sK2,k2_zfmisc_1(X0,X1))
        | ~ r1_tarski(k2_relat_1(sK2),X1)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f443,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',t119_zfmisc_1)).

fof(f443,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),X0)
        | r1_tarski(sK2,X0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f126,f72])).

fof(f72,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)),X1) ) ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',t21_relat_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',t1_xboole_1)).

fof(f398,plain,
    ( ~ spl4_63
    | spl4_64
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f385,f157,f99,f396,f390])).

fof(f390,plain,
    ( spl4_63
  <=> ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f396,plain,
    ( spl4_64
  <=> r1_tarski(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f157,plain,
    ( spl4_16
  <=> k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f385,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ r1_tarski(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl4_8
    | ~ spl4_16 ),
    inference(superposition,[],[f360,f158])).

fof(f158,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f360,plain,
    ( ! [X5] :
        ( r1_tarski(sK3(k1_zfmisc_1(X5)),sK1)
        | ~ r1_tarski(X5,k2_relat_1(sK2)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f132,f100])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(sK3(k1_zfmisc_1(X0)),X2) ) ),
    inference(resolution,[],[f129,f63])).

fof(f129,plain,(
    ! [X4,X5] :
      ( r1_tarski(sK3(k1_zfmisc_1(X4)),X5)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f63,f110])).

fof(f110,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f58,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',existence_m1_subset_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',t3_subset)).

fof(f382,plain,
    ( ~ spl4_59
    | spl4_60
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f369,f157,f92,f380,f374])).

fof(f374,plain,
    ( spl4_59
  <=> ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f380,plain,
    ( spl4_60
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f369,plain,
    ( r1_tarski(k1_xboole_0,sK0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2))
    | ~ spl4_6
    | ~ spl4_16 ),
    inference(superposition,[],[f358,f158])).

fof(f358,plain,
    ( ! [X2] :
        ( r1_tarski(sK3(k1_zfmisc_1(X2)),sK0)
        | ~ r1_tarski(X2,k1_relat_1(sK2)) )
    | ~ spl4_6 ),
    inference(resolution,[],[f132,f93])).

fof(f356,plain,
    ( ~ spl4_55
    | spl4_56
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f134,f99,f354,f351])).

fof(f351,plain,
    ( spl4_55
  <=> ~ v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f354,plain,
    ( spl4_56
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),X0)
        | r1_tarski(k2_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)),X0)
        | r1_tarski(k2_relat_1(sK2),X0)
        | ~ v1_relat_1(sK1) )
    | ~ spl4_8 ),
    inference(resolution,[],[f131,f52])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK1,X0)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k2_relat_1(sK2),X1) )
    | ~ spl4_8 ),
    inference(resolution,[],[f128,f63])).

fof(f128,plain,
    ( ! [X3] :
        ( r1_tarski(k2_relat_1(sK2),X3)
        | ~ r1_tarski(sK1,X3) )
    | ~ spl4_8 ),
    inference(resolution,[],[f63,f100])).

fof(f346,plain,
    ( ~ spl4_51
    | spl4_52
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f133,f92,f344,f341])).

fof(f341,plain,
    ( spl4_51
  <=> ~ v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f344,plain,
    ( spl4_52
  <=> ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),X0)
        | r1_tarski(k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),X0)
        | r1_tarski(k1_relat_1(sK2),X0)
        | ~ v1_relat_1(sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f130,f52])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k1_relat_1(sK2),X1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f127,f63])).

fof(f127,plain,
    ( ! [X2] :
        ( r1_tarski(k1_relat_1(sK2),X2)
        | ~ r1_tarski(sK0,X2) )
    | ~ spl4_6 ),
    inference(resolution,[],[f63,f93])).

fof(f335,plain,
    ( ~ spl4_47
    | spl4_48
    | spl4_28
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f306,f99,f78,f208,f333,f327])).

fof(f327,plain,
    ( spl4_47
  <=> ~ r1_tarski(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f333,plain,
    ( spl4_48
  <=> v1_xboole_0(sK3(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f208,plain,
    ( spl4_28
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f78,plain,
    ( spl4_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f306,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | v1_xboole_0(sK3(k2_relat_1(sK2)))
    | ~ r1_tarski(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f286,f128])).

fof(f286,plain,
    ( ! [X4] :
        ( ~ r1_tarski(X4,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X4)
        | v1_xboole_0(sK3(X4)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f282,f136])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f135,f121])).

fof(f121,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f57,f54])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',t2_subset)).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f64,f79])).

fof(f79,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',t5_subset)).

fof(f282,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK3(X1),X2)
      | v1_xboole_0(X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f219,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | m1_subset_1(sK3(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f62,f121])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',t4_subset)).

fof(f322,plain,
    ( ~ spl4_43
    | spl4_44
    | spl4_24
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f305,f92,f78,f195,f320,f314])).

fof(f314,plain,
    ( spl4_43
  <=> ~ r1_tarski(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f320,plain,
    ( spl4_44
  <=> v1_xboole_0(sK3(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f195,plain,
    ( spl4_24
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f305,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | v1_xboole_0(sK3(k1_relat_1(sK2)))
    | ~ r1_tarski(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f286,f127])).

fof(f273,plain,
    ( ~ spl4_41
    | spl4_39 ),
    inference(avatar_split_clause,[],[f266,f263,f271])).

fof(f271,plain,
    ( spl4_41
  <=> ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f263,plain,
    ( spl4_39
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f266,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_39 ),
    inference(resolution,[],[f264,f59])).

fof(f264,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f263])).

fof(f265,plain,
    ( ~ spl4_39
    | ~ spl4_2
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f255,f237,f78,f263])).

fof(f237,plain,
    ( spl4_34
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f255,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_34 ),
    inference(resolution,[],[f238,f135])).

fof(f238,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f237])).

fof(f253,plain,
    ( spl4_36
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f244,f224,f157,f143,f251])).

fof(f251,plain,
    ( spl4_36
  <=> k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f143,plain,
    ( spl4_14
  <=> v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f224,plain,
    ( spl4_30
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f244,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl4_14
    | ~ spl4_16
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f240,f158])).

fof(f240,plain,
    ( k1_zfmisc_1(k1_xboole_0) = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14
    | ~ spl4_30 ),
    inference(resolution,[],[f225,f147])).

fof(f147,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(k1_xboole_0)) = X2 )
    | ~ spl4_14 ),
    inference(resolution,[],[f144,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',t8_boole)).

fof(f144,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f143])).

fof(f225,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f224])).

fof(f239,plain,
    ( spl4_30
    | spl4_34
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f164,f157,f237,f224])).

fof(f164,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f121,f158])).

fof(f232,plain,
    ( spl4_30
    | ~ spl4_33
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f163,f157,f230,f224])).

fof(f230,plain,
    ( spl4_33
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f163,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f124,f158])).

fof(f124,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK3(X1))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f121,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',antisymmetry_r2_hidden)).

fof(f210,plain,
    ( ~ spl4_27
    | spl4_28
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f150,f99,f78,f208,f202])).

fof(f202,plain,
    ( spl4_27
  <=> ~ r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f150,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f138,f128])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f136,f59])).

fof(f197,plain,
    ( ~ spl4_23
    | spl4_24
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f149,f92,f78,f195,f189])).

fof(f189,plain,
    ( spl4_23
  <=> ~ r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f149,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ r1_tarski(sK0,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f138,f127])).

fof(f181,plain,
    ( spl4_20
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f165,f157,f179])).

fof(f179,plain,
    ( spl4_20
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f165,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f54,f158])).

fof(f172,plain,
    ( spl4_18
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f162,f157,f170])).

fof(f170,plain,
    ( spl4_18
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f162,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_16 ),
    inference(superposition,[],[f110,f158])).

fof(f159,plain,
    ( spl4_16
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f148,f143,f157])).

fof(f148,plain,
    ( k1_xboole_0 = sK3(k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_14 ),
    inference(resolution,[],[f144,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',t6_boole)).

fof(f145,plain,
    ( spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f137,f78,f143])).

fof(f137,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f136,f54])).

fof(f119,plain,
    ( ~ spl4_13
    | spl4_11 ),
    inference(avatar_split_clause,[],[f111,f106,f117])).

fof(f106,plain,
    ( spl4_11
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f111,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(resolution,[],[f59,f107])).

fof(f107,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f108,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f49,f106])).

fof(f49,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & r1_tarski(k2_relat_1(sK2),sK1)
    & r1_tarski(k1_relat_1(sK2),sK0)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & r1_tarski(k2_relat_1(X2),X1)
        & r1_tarski(k1_relat_1(X2),X0)
        & v1_relat_1(X2) )
   => ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & r1_tarski(k2_relat_1(sK2),sK1)
      & r1_tarski(k1_relat_1(sK2),sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & r1_tarski(k2_relat_1(X2),X1)
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & r1_tarski(k2_relat_1(X2),X1)
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r1_tarski(k2_relat_1(X2),X1)
            & r1_tarski(k1_relat_1(X2),X0) )
         => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',t11_relset_1)).

fof(f101,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f48,f99])).

fof(f48,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f47,f92])).

fof(f47,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f51,f85])).

fof(f85,plain,
    ( spl4_4
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f51,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',d2_xboole_0)).

fof(f80,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f66,f78])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f50,f51])).

fof(f50,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/relset_1__t11_relset_1.p',dt_o_0_0_xboole_0)).

fof(f73,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f46,f71])).

fof(f46,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
