%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t9_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:53 EDT 2019

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 721 expanded)
%              Number of leaves         :   36 ( 203 expanded)
%              Depth                    :   21
%              Number of atoms          :  753 (3711 expanded)
%              Number of equality atoms :  134 ( 937 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9706,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f98,f100,f293,f2740,f2833,f4241,f4527,f4695,f4728,f4872,f5106,f5159,f5167,f5181,f5346,f6700,f7835,f8239,f8272,f9705])).

fof(f9705,plain,
    ( spl5_3
    | ~ spl5_18
    | ~ spl5_26
    | ~ spl5_276
    | ~ spl5_400 ),
    inference(avatar_contradiction_clause,[],[f9704])).

fof(f9704,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_18
    | ~ spl5_26
    | ~ spl5_276
    | ~ spl5_400 ),
    inference(subsumption_resolution,[],[f9703,f4544])).

fof(f4544,plain,
    ( v1_xboole_0(sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f4543])).

fof(f4543,plain,
    ( spl5_18
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f9703,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_3
    | ~ spl5_26
    | ~ spl5_276
    | ~ spl5_400 ),
    inference(duplicate_literal_removal,[],[f9701])).

fof(f9701,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK1)
    | ~ spl5_3
    | ~ spl5_26
    | ~ spl5_276
    | ~ spl5_400 ),
    inference(resolution,[],[f9674,f8276])).

fof(f8276,plain,
    ( ! [X0] :
        ( v1_funct_2(X0,sK0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_26 ),
    inference(superposition,[],[f8100,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t6_boole)).

fof(f8100,plain,
    ( v1_funct_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f50,f200])).

fof(f200,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl5_26
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f50,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t9_funct_2)).

fof(f9674,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_3
    | ~ spl5_26
    | ~ spl5_276
    | ~ spl5_400 ),
    inference(superposition,[],[f9669,f56])).

fof(f9669,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_26
    | ~ spl5_276
    | ~ spl5_400 ),
    inference(backward_demodulation,[],[f9667,f8196])).

fof(f8196,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK0,sK2)
    | ~ spl5_3
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f87,f200])).

fof(f87,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_3
  <=> ~ v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f9667,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3
    | ~ spl5_26
    | ~ spl5_276
    | ~ spl5_400 ),
    inference(subsumption_resolution,[],[f9664,f52])).

fof(f52,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f9664,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_3
    | ~ spl5_26
    | ~ spl5_276
    | ~ spl5_400 ),
    inference(resolution,[],[f8273,f8196])).

fof(f8273,plain,
    ( ! [X47] :
        ( v1_funct_2(k1_xboole_0,sK0,X47)
        | k1_xboole_0 = X47
        | ~ r1_tarski(sK1,X47) )
    | ~ spl5_26
    | ~ spl5_276
    | ~ spl5_400 ),
    inference(forward_demodulation,[],[f8237,f8202])).

fof(f8202,plain,
    ( k1_relat_1(k1_xboole_0) = sK0
    | ~ spl5_26
    | ~ spl5_276 ),
    inference(forward_demodulation,[],[f5141,f200])).

fof(f5141,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl5_276 ),
    inference(avatar_component_clause,[],[f5140])).

fof(f5140,plain,
    ( spl5_276
  <=> k1_relat_1(sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_276])])).

fof(f8237,plain,
    ( ! [X47] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X47)
        | k1_xboole_0 = X47
        | ~ r1_tarski(sK1,X47) )
    | ~ spl5_400 ),
    inference(avatar_component_clause,[],[f8236])).

fof(f8236,plain,
    ( spl5_400
  <=> ! [X47] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X47)
        | k1_xboole_0 = X47
        | ~ r1_tarski(sK1,X47) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_400])])).

fof(f8272,plain,
    ( ~ spl5_26
    | ~ spl5_42
    | ~ spl5_276
    | spl5_399 ),
    inference(avatar_contradiction_clause,[],[f8271])).

fof(f8271,plain,
    ( $false
    | ~ spl5_26
    | ~ spl5_42
    | ~ spl5_276
    | ~ spl5_399 ),
    inference(subsumption_resolution,[],[f8270,f8199])).

fof(f8199,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl5_26
    | ~ spl5_42 ),
    inference(backward_demodulation,[],[f8197,f8140])).

fof(f8140,plain,
    ( r1_tarski(k1_relset_1(sK0,sK1,k1_xboole_0),sK0)
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f4432,f200])).

fof(f4432,plain,(
    r1_tarski(k1_relset_1(sK0,sK1,sK3),sK0) ),
    inference(resolution,[],[f51,f140])).

fof(f140,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | r1_tarski(k1_relset_1(X9,X10,X8),X9) ) ),
    inference(resolution,[],[f67,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t3_subset)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',dt_k1_relset_1)).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f8197,plain,
    ( k1_relset_1(sK0,sK1,k1_xboole_0) = sK0
    | ~ spl5_26
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f244,f200])).

fof(f244,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl5_42
  <=> k1_relset_1(sK0,sK1,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f8270,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl5_26
    | ~ spl5_276
    | ~ spl5_399 ),
    inference(forward_demodulation,[],[f8234,f8202])).

fof(f8234,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(k1_xboole_0))
    | ~ spl5_399 ),
    inference(avatar_component_clause,[],[f8233])).

fof(f8233,plain,
    ( spl5_399
  <=> ~ r1_tarski(sK0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_399])])).

fof(f8239,plain,
    ( ~ spl5_399
    | spl5_400
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f8222,f199,f8236,f8233])).

fof(f8222,plain,
    ( ! [X64] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X64)
        | ~ r1_tarski(sK0,k1_relat_1(k1_xboole_0))
        | ~ r1_tarski(sK1,X64)
        | k1_xboole_0 = X64 )
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f8221,f200])).

fof(f8221,plain,
    ( ! [X64] :
        ( ~ r1_tarski(sK0,k1_relat_1(k1_xboole_0))
        | ~ r1_tarski(sK1,X64)
        | k1_xboole_0 = X64
        | v1_funct_2(sK3,k1_relat_1(sK3),X64) )
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f4520,f200])).

fof(f4520,plain,(
    ! [X64] :
      ( ~ r1_tarski(sK0,k1_relat_1(sK3))
      | ~ r1_tarski(sK1,X64)
      | k1_xboole_0 = X64
      | v1_funct_2(sK3,k1_relat_1(sK3),X64) ) ),
    inference(resolution,[],[f2704,f580])).

fof(f580,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | k1_xboole_0 = X1
      | v1_funct_2(X0,k1_relat_1(X0),X1) ) ),
    inference(equality_resolution,[],[f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f70,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',redefinition_k1_relset_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',d1_funct_2)).

fof(f2704,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r1_tarski(sK0,X1)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f51,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t17_relset_1)).

fof(f7835,plain,
    ( spl5_3
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_168
    | ~ spl5_170
    | ~ spl5_260 ),
    inference(avatar_contradiction_clause,[],[f7834])).

fof(f7834,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_18
    | ~ spl5_168
    | ~ spl5_170
    | ~ spl5_260 ),
    inference(subsumption_resolution,[],[f7833,f4544])).

fof(f7833,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_168
    | ~ spl5_170
    | ~ spl5_260 ),
    inference(duplicate_literal_removal,[],[f7831])).

fof(f7831,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ v1_xboole_0(sK1)
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_168
    | ~ spl5_170
    | ~ spl5_260 ),
    inference(resolution,[],[f7797,f4794])).

fof(f4794,plain,
    ( ! [X0] :
        ( v1_funct_2(sK3,X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_170 ),
    inference(superposition,[],[f4732,f56])).

fof(f4732,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_170 ),
    inference(avatar_component_clause,[],[f4731])).

fof(f4731,plain,
    ( spl5_170
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_170])])).

fof(f7797,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,X0,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_168
    | ~ spl5_260 ),
    inference(superposition,[],[f7792,f56])).

fof(f7792,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_168
    | ~ spl5_260 ),
    inference(backward_demodulation,[],[f7790,f6740])).

fof(f6740,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl5_3
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f87,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_8
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f7790,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_168
    | ~ spl5_260 ),
    inference(subsumption_resolution,[],[f7785,f52])).

fof(f7785,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK2
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_168
    | ~ spl5_260 ),
    inference(resolution,[],[f6706,f6740])).

fof(f6706,plain,
    ( ! [X64] :
        ( v1_funct_2(sK3,k1_xboole_0,X64)
        | ~ r1_tarski(sK1,X64)
        | k1_xboole_0 = X64 )
    | ~ spl5_8
    | ~ spl5_168
    | ~ spl5_260 ),
    inference(forward_demodulation,[],[f5563,f5103])).

fof(f5103,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ spl5_260 ),
    inference(avatar_component_clause,[],[f5102])).

fof(f5102,plain,
    ( spl5_260
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_260])])).

fof(f5563,plain,
    ( ! [X64] :
        ( ~ r1_tarski(sK1,X64)
        | k1_xboole_0 = X64
        | v1_funct_2(sK3,k1_relat_1(sK3),X64) )
    | ~ spl5_8
    | ~ spl5_168
    | ~ spl5_260 ),
    inference(subsumption_resolution,[],[f5562,f5239])).

fof(f5239,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_168 ),
    inference(forward_demodulation,[],[f5230,f2736])).

fof(f2736,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl5_168 ),
    inference(avatar_component_clause,[],[f2735])).

fof(f2735,plain,
    ( spl5_168
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_168])])).

fof(f5230,plain,
    ( r1_tarski(k1_relset_1(k1_xboole_0,sK1,sK3),k1_xboole_0)
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f97,f4432])).

fof(f5562,plain,
    ( ! [X64] :
        ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
        | ~ r1_tarski(sK1,X64)
        | k1_xboole_0 = X64
        | v1_funct_2(sK3,k1_relat_1(sK3),X64) )
    | ~ spl5_8
    | ~ spl5_260 ),
    inference(forward_demodulation,[],[f5561,f97])).

fof(f5561,plain,
    ( ! [X64] :
        ( ~ r1_tarski(sK0,k1_xboole_0)
        | ~ r1_tarski(sK1,X64)
        | k1_xboole_0 = X64
        | v1_funct_2(sK3,k1_relat_1(sK3),X64) )
    | ~ spl5_260 ),
    inference(forward_demodulation,[],[f4520,f5103])).

fof(f6700,plain,
    ( spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_168 ),
    inference(avatar_contradiction_clause,[],[f6699])).

fof(f6699,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_168 ),
    inference(subsumption_resolution,[],[f6698,f5544])).

fof(f5544,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f52,f247])).

fof(f247,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl5_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f6698,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_168 ),
    inference(subsumption_resolution,[],[f6687,f5239])).

fof(f6687,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(resolution,[],[f6682,f5386])).

fof(f5386,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k1_xboole_0,X1)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl5_6
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f5202,f247])).

fof(f5202,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r1_tarski(k1_xboole_0,X1)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f97,f2704])).

fof(f6682,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f90,f97])).

fof(f90,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_5
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f5346,plain,
    ( ~ spl5_8
    | ~ spl5_76
    | spl5_167 ),
    inference(avatar_contradiction_clause,[],[f5345])).

fof(f5345,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_76
    | ~ spl5_167 ),
    inference(subsumption_resolution,[],[f5344,f1084])).

fof(f1084,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f1083,plain,
    ( spl5_76
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f5344,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_167 ),
    inference(forward_demodulation,[],[f2733,f97])).

fof(f2733,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_167 ),
    inference(avatar_component_clause,[],[f2732])).

fof(f2732,plain,
    ( spl5_167
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f5181,plain,
    ( spl5_42
    | spl5_6 ),
    inference(avatar_split_clause,[],[f5180,f246,f243])).

fof(f5180,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(subsumption_resolution,[],[f2703,f50])).

fof(f2703,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(resolution,[],[f51,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5167,plain,
    ( ~ spl5_235
    | spl5_26
    | spl5_8
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f5166,f4543,f96,f199,f4535])).

fof(f4535,plain,
    ( spl5_235
  <=> ~ v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_235])])).

fof(f5166,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f4459,f4544])).

fof(f4459,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f102,f523])).

fof(f523,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | ~ v1_funct_2(X1,X2,k1_xboole_0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f150,f56])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,k1_xboole_0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X1,k1_xboole_0) ) ),
    inference(resolution,[],[f79,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f79,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f62,f51])).

fof(f5159,plain,
    ( spl5_276
    | spl5_6 ),
    inference(avatar_split_clause,[],[f5158,f246,f5140])).

fof(f5158,plain,
    ( k1_xboole_0 = sK1
    | k1_relat_1(sK3) = sK0 ),
    inference(global_subsumption,[],[f5138])).

fof(f5138,plain,
    ( k1_xboole_0 = sK1
    | k1_relat_1(sK3) = sK0 ),
    inference(global_subsumption,[],[f50,f4441])).

fof(f4441,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | k1_relat_1(sK3) = sK0 ),
    inference(resolution,[],[f51,f626])).

fof(f626,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_xboole_0 = X4
      | ~ v1_funct_2(X5,X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f615,f62])).

fof(f615,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | k1_xboole_0 = X4
      | ~ v1_funct_2(X5,X3,X4)
      | ~ r1_tarski(X5,k2_zfmisc_1(X3,X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f165,f66])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X2,X0) = X1
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X0,X1,X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f68,f63])).

fof(f5106,plain,
    ( ~ spl5_223
    | spl5_260
    | ~ spl5_168 ),
    inference(avatar_split_clause,[],[f4702,f2735,f5102,f4398])).

fof(f4398,plain,
    ( spl5_223
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_223])])).

fof(f4702,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_168 ),
    inference(superposition,[],[f66,f2736])).

fof(f4872,plain,
    ( ~ spl5_18
    | spl5_235 ),
    inference(avatar_contradiction_clause,[],[f4871])).

fof(f4871,plain,
    ( $false
    | ~ spl5_18
    | ~ spl5_235 ),
    inference(subsumption_resolution,[],[f4544,f4721])).

fof(f4721,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_235 ),
    inference(resolution,[],[f4634,f50])).

fof(f4634,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK0,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_235 ),
    inference(superposition,[],[f4536,f56])).

fof(f4536,plain,
    ( ~ v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl5_235 ),
    inference(avatar_component_clause,[],[f4535])).

fof(f4728,plain,
    ( ~ spl5_166
    | spl5_223 ),
    inference(avatar_contradiction_clause,[],[f4727])).

fof(f4727,plain,
    ( $false
    | ~ spl5_166
    | ~ spl5_223 ),
    inference(subsumption_resolution,[],[f4722,f4403])).

fof(f4403,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_166 ),
    inference(avatar_component_clause,[],[f4402])).

fof(f4402,plain,
    ( spl5_166
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f4722,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_223 ),
    inference(resolution,[],[f4563,f51])).

fof(f4563,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_xboole_0(X0) )
    | ~ spl5_223 ),
    inference(superposition,[],[f4399,f56])).

fof(f4399,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_223 ),
    inference(avatar_component_clause,[],[f4398])).

fof(f4695,plain,
    ( ~ spl5_166
    | spl5_171 ),
    inference(avatar_contradiction_clause,[],[f4694])).

fof(f4694,plain,
    ( $false
    | ~ spl5_166
    | ~ spl5_171 ),
    inference(subsumption_resolution,[],[f4693,f4403])).

fof(f4693,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl5_171 ),
    inference(resolution,[],[f4557,f50])).

fof(f4557,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,X0,sK1)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_171 ),
    inference(superposition,[],[f2739,f56])).

fof(f2739,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl5_171 ),
    inference(avatar_component_clause,[],[f2738])).

fof(f2738,plain,
    ( spl5_171
  <=> ~ v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_171])])).

fof(f4527,plain,
    ( spl5_5
    | ~ spl5_42 ),
    inference(avatar_contradiction_clause,[],[f4526])).

fof(f4526,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f4525,f52])).

fof(f4525,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl5_5
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f4492,f2721])).

fof(f2721,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f2705,f244])).

fof(f2705,plain,(
    r1_tarski(k1_relset_1(sK0,sK1,sK3),sK0) ),
    inference(resolution,[],[f51,f140])).

fof(f4492,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f2704,f90])).

fof(f4241,plain,
    ( spl5_3
    | spl5_7
    | spl5_19
    | ~ spl5_42
    | ~ spl5_76 ),
    inference(avatar_contradiction_clause,[],[f4240])).

fof(f4240,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_19
    | ~ spl5_42
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f4239,f1084])).

fof(f4239,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_19
    | ~ spl5_42 ),
    inference(backward_demodulation,[],[f4235,f4146])).

fof(f4146,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f1293,f130])).

fof(f130,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_19
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1293,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f226,f52])).

fof(f226,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f117,f106])).

fof(f106,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f61,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f12,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',existence_m1_subset_1)).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t2_subset)).

fof(f117,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X4,X5)
      | ~ v1_xboole_0(X3)
      | ~ r1_tarski(X5,X3) ) ),
    inference(resolution,[],[f75,f63])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',t5_subset)).

fof(f4235,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f4121,f52])).

fof(f4121,plain,
    ( ~ r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK2
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_42 ),
    inference(resolution,[],[f2825,f87])).

fof(f2825,plain,
    ( ! [X47] :
        ( v1_funct_2(sK3,sK0,X47)
        | ~ r1_tarski(sK1,X47)
        | k1_xboole_0 = X47 )
    | ~ spl5_7
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f2824,f2726])).

fof(f2726,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f2725,f50])).

fof(f2725,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_relat_1(sK3) = sK0
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f2714,f94])).

fof(f94,plain,
    ( k1_xboole_0 != sK1
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl5_7
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f2714,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | k1_relat_1(sK3) = sK0 ),
    inference(resolution,[],[f51,f626])).

fof(f2824,plain,
    ( ! [X47] :
        ( ~ r1_tarski(sK1,X47)
        | k1_xboole_0 = X47
        | v1_funct_2(sK3,k1_relat_1(sK3),X47) )
    | ~ spl5_7
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f2823,f2721])).

fof(f2823,plain,
    ( ! [X47] :
        ( ~ r1_tarski(sK0,sK0)
        | ~ r1_tarski(sK1,X47)
        | k1_xboole_0 = X47
        | v1_funct_2(sK3,k1_relat_1(sK3),X47) )
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f2801,f2726])).

fof(f2801,plain,(
    ! [X47] :
      ( ~ r1_tarski(sK0,k1_relat_1(sK3))
      | ~ r1_tarski(sK1,X47)
      | k1_xboole_0 = X47
      | v1_funct_2(sK3,k1_relat_1(sK3),X47) ) ),
    inference(resolution,[],[f2704,f580])).

fof(f2833,plain,(
    spl5_77 ),
    inference(avatar_contradiction_clause,[],[f2829])).

fof(f2829,plain,
    ( $false
    | ~ spl5_77 ),
    inference(resolution,[],[f2759,f55])).

fof(f55,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t9_funct_2.p',dt_o_0_0_xboole_0)).

fof(f2759,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl5_77 ),
    inference(duplicate_literal_removal,[],[f2758])).

fof(f2758,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_77 ),
    inference(superposition,[],[f2687,f56])).

fof(f2687,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f2686])).

fof(f2686,plain,
    ( spl5_77
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f2740,plain,
    ( ~ spl5_167
    | spl5_168
    | ~ spl5_171 ),
    inference(avatar_split_clause,[],[f2708,f2738,f2735,f2732])).

fof(f2708,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f51,f160])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X1,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X2,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f81,f56])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f293,plain,
    ( ~ spl5_6
    | spl5_19 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(resolution,[],[f286,f55])).

fof(f286,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(superposition,[],[f269,f56])).

fof(f269,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f247,f130])).

fof(f100,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f84,f49])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,
    ( ~ v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_1
  <=> ~ v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f98,plain,
    ( ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f53,f96,f93])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f91,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f54,f89,f86,f83])).

fof(f54,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
