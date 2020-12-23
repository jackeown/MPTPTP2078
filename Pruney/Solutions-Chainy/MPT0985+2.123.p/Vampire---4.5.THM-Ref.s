%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 487 expanded)
%              Number of leaves         :   25 ( 142 expanded)
%              Depth                    :   19
%              Number of atoms          :  609 (2485 expanded)
%              Number of equality atoms :  107 ( 438 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f441,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f92,f100,f106,f122,f124,f127,f173,f207,f285,f303,f347,f357,f430,f440])).

fof(f440,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f438,f413])).

fof(f413,plain,
    ( ! [X0] : v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f412,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f412,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f411,f276])).

fof(f276,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl3_21
  <=> k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f411,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X0)
        | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f410,f189])).

fof(f189,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_13
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f410,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f409,f189])).

fof(f409,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f165,f121])).

fof(f121,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f165,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f164,f91])).

fof(f91,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f164,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f162,f72])).

fof(f72,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f162,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_6 ),
    inference(superposition,[],[f47,f161])).

fof(f161,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f99,f160])).

fof(f160,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f110,f37])).

fof(f37,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27])).

fof(f27,plain,
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
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f110,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f35,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_6
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f438,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f437,f189])).

fof(f437,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f77,f121])).

fof(f77,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f430,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(resolution,[],[f421,f394])).

fof(f394,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f224,f189])).

fof(f224,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f81,f121])).

fof(f81,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f421,plain,
    ( ! [X1] : m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f420,f41])).

fof(f420,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f419,f276])).

fof(f419,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X1)
        | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f418,f189])).

fof(f418,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f417,f189])).

fof(f417,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f168,f121])).

fof(f168,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f167,f91])).

fof(f167,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f163,f72])).

fof(f163,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_6 ),
    inference(superposition,[],[f48,f161])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f357,plain,
    ( ~ spl3_18
    | spl3_21
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f356,f187,f274,f254])).

fof(f254,plain,
    ( spl3_18
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f356,plain,
    ( k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f355,f39])).

fof(f39,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f355,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f351,f243])).

fof(f243,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f33,f189])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f351,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl3_13 ),
    inference(resolution,[],[f244,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f244,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f36,f189])).

fof(f36,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f347,plain,
    ( spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f339,f321])).

fof(f321,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f314,f305])).

fof(f305,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f221,f193])).

fof(f193,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_14
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f221,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f34,f121])).

fof(f34,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f314,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(resolution,[],[f304,f69])).

fof(f69,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f304,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f222,f193])).

fof(f222,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f35,f121])).

fof(f339,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl3_8
    | ~ spl3_9
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f338,f193])).

fof(f338,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f116,f121])).

fof(f116,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_8
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f303,plain,
    ( spl3_13
    | spl3_14
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f302,f119,f191,f187])).

fof(f302,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f296,f221])).

fof(f296,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl3_9 ),
    inference(resolution,[],[f222,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f285,plain,
    ( ~ spl3_4
    | ~ spl3_13
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_13
    | spl3_18 ),
    inference(subsumption_resolution,[],[f256,f246])).

fof(f246,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f86,f189])).

fof(f86,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f256,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl3_18 ),
    inference(avatar_component_clause,[],[f254])).

fof(f207,plain,
    ( ~ spl3_1
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl3_1
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f199,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f199,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl3_1
    | spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f169,f81])).

fof(f169,plain,
    ( ! [X1] :
        ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ r1_tarski(sK0,X1) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f168,f153])).

fof(f153,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f105,f152])).

fof(f152,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f109,f117])).

fof(f117,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f109,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f35,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f105,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_7
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f173,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f171,f64])).

fof(f171,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(resolution,[],[f166,f77])).

fof(f166,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(sK0,X0) )
    | ~ spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f165,f153])).

fof(f127,plain,
    ( spl3_1
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl3_1
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f125,f86])).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f107,f33])).

fof(f107,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(resolution,[],[f73,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f73,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f124,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f111,f87])).

fof(f87,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f111,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f35,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f122,plain,
    ( spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f113,f119,f115])).

fof(f113,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f108,f34])).

fof(f108,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f35,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f106,plain,
    ( ~ spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f101,f103,f85])).

fof(f101,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f94,f33])).

fof(f94,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f36,f45])).

fof(f100,plain,
    ( ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f95,f97,f85])).

fof(f95,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f93,f33])).

fof(f93,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f36,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f92,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f83,f89,f85])).

fof(f83,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f38,f79,f75,f71])).

fof(f38,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (25424)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.47  % (25439)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.47  % (25431)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.48  % (25414)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % (25415)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.48  % (25436)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.48  % (25416)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.48  % (25428)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (25418)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (25426)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (25435)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.49  % (25420)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (25427)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (25425)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (25434)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (25433)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (25422)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (25415)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f441,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f82,f92,f100,f106,f122,f124,f127,f173,f207,f285,f303,f347,f357,f430,f440])).
% 0.21/0.50  fof(f440,plain,(
% 0.21/0.50    ~spl3_1 | spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13 | ~spl3_21),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f439])).
% 0.21/0.50  fof(f439,plain,(
% 0.21/0.50    $false | (~spl3_1 | spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13 | ~spl3_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f438,f413])).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13 | ~spl3_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f412,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.50  fof(f412,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13 | ~spl3_21)),
% 0.21/0.50    inference(forward_demodulation,[],[f411,f276])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~spl3_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f274])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    spl3_21 <=> k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.50  fof(f411,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X0) | v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f410,f189])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f187])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    spl3_13 <=> k1_xboole_0 = sK2),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f409,f189])).
% 0.21/0.50  fof(f409,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_9)),
% 0.21/0.50    inference(forward_demodulation,[],[f165,f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl3_9 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f164,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl3_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_1 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f162,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl3_6),
% 0.21/0.50    inference(superposition,[],[f47,f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_6),
% 0.21/0.50    inference(backward_demodulation,[],[f99,f160])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK2)),
% 0.21/0.50    inference(forward_demodulation,[],[f110,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f35,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl3_6 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_2 | ~spl3_9 | ~spl3_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f437,f189])).
% 0.21/0.50  fof(f437,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_2 | ~spl3_9)),
% 0.21/0.50    inference(forward_demodulation,[],[f77,f121])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f430,plain,(
% 0.21/0.50    ~spl3_1 | spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13 | ~spl3_21),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f422])).
% 0.21/0.50  fof(f422,plain,(
% 0.21/0.50    $false | (~spl3_1 | spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13 | ~spl3_21)),
% 0.21/0.50    inference(resolution,[],[f421,f394])).
% 0.21/0.50  fof(f394,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_9 | ~spl3_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f224,f189])).
% 0.21/0.50  fof(f224,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_9)),
% 0.21/0.50    inference(backward_demodulation,[],[f81,f121])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f421,plain,(
% 0.21/0.50    ( ! [X1] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13 | ~spl3_21)),
% 0.21/0.50    inference(subsumption_resolution,[],[f420,f41])).
% 0.21/0.50  fof(f420,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(k1_xboole_0,X1) | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13 | ~spl3_21)),
% 0.21/0.50    inference(forward_demodulation,[],[f419,f276])).
% 0.21/0.50  fof(f419,plain,(
% 0.21/0.50    ( ! [X1] : (~r1_tarski(k2_relat_1(k2_funct_1(k1_xboole_0)),X1) | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f418,f189])).
% 0.21/0.50  fof(f418,plain,(
% 0.21/0.50    ( ! [X1] : (m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_9 | ~spl3_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f417,f189])).
% 0.21/0.50  fof(f417,plain,(
% 0.21/0.50    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_9)),
% 0.21/0.50    inference(forward_demodulation,[],[f168,f121])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f167,f91])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_1 | ~spl3_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f163,f72])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X1) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl3_6),
% 0.21/0.50    inference(superposition,[],[f48,f161])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f357,plain,(
% 0.21/0.50    ~spl3_18 | spl3_21 | ~spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f356,f187,f274,f254])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    spl3_18 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f356,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~spl3_13),
% 0.21/0.50    inference(forward_demodulation,[],[f355,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  fof(f355,plain,(
% 0.21/0.50    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~spl3_13),
% 0.21/0.50    inference(subsumption_resolution,[],[f351,f243])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    v1_funct_1(k1_xboole_0) | ~spl3_13),
% 0.21/0.50    inference(backward_demodulation,[],[f33,f189])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f351,plain,(
% 0.21/0.50    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl3_13),
% 0.21/0.50    inference(resolution,[],[f244,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    v2_funct_1(k1_xboole_0) | ~spl3_13),
% 0.21/0.50    inference(backward_demodulation,[],[f36,f189])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    v2_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    spl3_8 | ~spl3_9 | ~spl3_14),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f346])).
% 0.21/0.50  fof(f346,plain,(
% 0.21/0.50    $false | (spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f339,f321])).
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl3_9 | ~spl3_14)),
% 0.21/0.50    inference(subsumption_resolution,[],[f314,f305])).
% 0.21/0.50  fof(f305,plain,(
% 0.21/0.50    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_9 | ~spl3_14)),
% 0.21/0.50    inference(backward_demodulation,[],[f221,f193])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl3_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f191])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    spl3_14 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f221,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl3_9),
% 0.21/0.50    inference(backward_demodulation,[],[f34,f121])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl3_9 | ~spl3_14)),
% 0.21/0.50    inference(resolution,[],[f304,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_9 | ~spl3_14)),
% 0.21/0.50    inference(backward_demodulation,[],[f222,f193])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl3_9),
% 0.21/0.50    inference(backward_demodulation,[],[f35,f121])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl3_8 | ~spl3_9 | ~spl3_14)),
% 0.21/0.50    inference(forward_demodulation,[],[f338,f193])).
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl3_8 | ~spl3_9)),
% 0.21/0.50    inference(forward_demodulation,[],[f116,f121])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    sK0 != k1_relset_1(sK0,sK1,sK2) | spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl3_8 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    spl3_13 | spl3_14 | ~spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f302,f119,f191,f187])).
% 0.21/0.50  fof(f302,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl3_9),
% 0.21/0.50    inference(subsumption_resolution,[],[f296,f221])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl3_9),
% 0.21/0.50    inference(resolution,[],[f222,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.21/0.50    inference(equality_resolution,[],[f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    ~spl3_4 | ~spl3_13 | spl3_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f284])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    $false | (~spl3_4 | ~spl3_13 | spl3_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f256,f246])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    v1_relat_1(k1_xboole_0) | (~spl3_4 | ~spl3_13)),
% 0.21/0.50    inference(backward_demodulation,[],[f86,f189])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl3_4 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    ~v1_relat_1(k1_xboole_0) | spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f254])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    ~spl3_1 | spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f206])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    $false | (~spl3_1 | spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f199,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    ~r1_tarski(sK0,sK0) | (~spl3_1 | spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(resolution,[],[f169,f81])).
% 0.21/0.50  fof(f169,plain,(
% 0.21/0.50    ( ! [X1] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~r1_tarski(sK0,X1)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(forward_demodulation,[],[f168,f153])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    sK0 = k2_relat_1(k2_funct_1(sK2)) | (~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(backward_demodulation,[],[f105,f152])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK2) | ~spl3_8),
% 0.21/0.50    inference(forward_demodulation,[],[f109,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(resolution,[],[f35,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl3_7 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ~spl3_1 | spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f172])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    $false | (~spl3_1 | spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(subsumption_resolution,[],[f171,f64])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ~r1_tarski(sK0,sK0) | (~spl3_1 | spl3_2 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(resolution,[],[f166,f77])).
% 0.21/0.50  fof(f166,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(sK0,X0)) ) | (~spl3_1 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_8)),
% 0.21/0.50    inference(forward_demodulation,[],[f165,f153])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl3_1 | ~spl3_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    $false | (spl3_1 | ~spl3_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f125,f86])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | spl3_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f107,f33])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.21/0.50    inference(resolution,[],[f73,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f71])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    $false | spl3_4),
% 0.21/0.50    inference(subsumption_resolution,[],[f111,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f35,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl3_8 | spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f113,f119,f115])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f108,f34])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(resolution,[],[f35,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ~spl3_4 | spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f101,f103,f85])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f94,f33])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f36,f45])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ~spl3_4 | spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f95,f97,f85])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f93,f33])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f36,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ~spl3_4 | spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f83,f89,f85])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f33,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f79,f75,f71])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (25415)------------------------------
% 0.21/0.50  % (25415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25415)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (25415)Memory used [KB]: 10746
% 0.21/0.50  % (25415)Time elapsed: 0.084 s
% 0.21/0.50  % (25415)------------------------------
% 0.21/0.50  % (25415)------------------------------
% 0.21/0.50  % (25419)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (25421)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (25417)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (25413)Success in time 0.153 s
%------------------------------------------------------------------------------
