%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t172_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:20 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 128 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :  217 ( 371 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f76,f82,f96,f100,f115,f124,f130,f195,f261,f265])).

fof(f265,plain,
    ( spl7_11
    | spl7_35
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl7_11
    | ~ spl7_35
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f263,f95])).

fof(f95,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl7_11
  <=> ~ r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f263,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2),sK0)
    | ~ spl7_35
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f262,f194])).

fof(f194,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_35
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f262,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(k1_funct_1(sK1,sK2),sK0)
    | ~ spl7_44 ),
    inference(resolution,[],[f260,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t172_funct_1.p',t2_subset)).

fof(f260,plain,
    ( m1_subset_1(k1_funct_1(sK1,sK2),sK0)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl7_44
  <=> m1_subset_1(k1_funct_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f261,plain,
    ( spl7_44
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f257,f128,f122,f259])).

fof(f122,plain,
    ( spl7_20
  <=> m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f128,plain,
    ( spl7_22
  <=> r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f257,plain,
    ( m1_subset_1(k1_funct_1(sK1,sK2),sK0)
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(resolution,[],[f146,f123])).

fof(f123,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f122])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(X0))
        | m1_subset_1(k1_funct_1(sK1,sK2),X0) )
    | ~ spl7_22 ),
    inference(resolution,[],[f129,f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t172_funct_1.p',t4_subset)).

fof(f129,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f128])).

fof(f195,plain,
    ( ~ spl7_35
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f188,f128,f122,f193])).

fof(f188,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(resolution,[],[f147,f123])).

fof(f147,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(X1))
        | ~ v1_xboole_0(X1) )
    | ~ spl7_22 ),
    inference(resolution,[],[f129,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t172_funct_1.p',t5_subset)).

fof(f130,plain,
    ( spl7_22
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f120,f113,f68,f64,f128])).

fof(f64,plain,
    ( spl7_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f68,plain,
    ( spl7_2
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f113,plain,
    ( spl7_18
  <=> sP4(k1_funct_1(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f120,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f119,f65])).

fof(f65,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f64])).

fof(f119,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1))
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f118,f69])).

fof(f69,plain,
    ( v1_funct_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f118,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1))
    | ~ spl7_18 ),
    inference(resolution,[],[f114,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t172_funct_1.p',d5_funct_1)).

fof(f114,plain,
    ( sP4(k1_funct_1(sK1,sK2),sK1)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f124,plain,
    ( spl7_20
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f110,f98,f122])).

fof(f98,plain,
    ( spl7_12
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f110,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl7_12 ),
    inference(resolution,[],[f99,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t172_funct_1.p',t3_subset)).

fof(f99,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f98])).

fof(f115,plain,
    ( spl7_18
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f83,f80,f113])).

fof(f80,plain,
    ( spl7_6
  <=> r2_hidden(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f83,plain,
    ( sP4(k1_funct_1(sK1,sK2),sK1)
    | ~ spl7_6 ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | sP4(k1_funct_1(X0,X3),X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,
    ( r2_hidden(sK2,k1_relat_1(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f100,plain,
    ( spl7_12
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f78,f74,f64,f98])).

fof(f74,plain,
    ( spl7_4
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f78,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl7_0
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f77,f65])).

fof(f77,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl7_4 ),
    inference(resolution,[],[f75,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t172_funct_1.p',d19_relat_1)).

fof(f75,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f96,plain,(
    ~ spl7_11 ),
    inference(avatar_split_clause,[],[f37,f94])).

fof(f37,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k1_relat_1(X1))
           => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t172_funct_1.p',t172_funct_1)).

fof(f82,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f36,f80])).

fof(f36,plain,(
    r2_hidden(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f70,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f40,f68])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f38,f64])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
