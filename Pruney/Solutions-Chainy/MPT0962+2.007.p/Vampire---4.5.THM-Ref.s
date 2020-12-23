%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 282 expanded)
%              Number of leaves         :   17 (  77 expanded)
%              Depth                    :   15
%              Number of atoms          :  254 ( 980 expanded)
%              Number of equality atoms :   51 ( 166 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f544,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f145,f238,f267,f385,f535,f543])).

fof(f543,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f540])).

fof(f540,plain,
    ( $false
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f42,f144])).

fof(f144,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f42,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f535,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f484,f488])).

fof(f488,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f483,f64])).

fof(f64,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f483,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f388,f465])).

fof(f465,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f71,f346,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f346,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_1
    | spl3_2 ),
    inference(forward_demodulation,[],[f308,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f308,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0))
    | ~ spl3_1
    | spl3_2 ),
    inference(backward_demodulation,[],[f224,f282])).

fof(f282,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_1
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f140,f135,f254,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f254,plain,
    ( k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f135,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f135,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f140,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_2
  <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f224,plain,(
    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) ),
    inference(unit_resulting_resolution,[],[f171,f100,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f100,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(X0,k2_relat_1(sK1)),k2_zfmisc_1(X0,sK0)) ),
    inference(unit_resulting_resolution,[],[f43,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f43,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f171,plain,(
    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f95,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f95,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))) ),
    inference(unit_resulting_resolution,[],[f41,f42,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f388,plain,
    ( v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f94,f387])).

fof(f387,plain,
    ( k1_xboole_0 = k2_relat_1(sK1)
    | ~ spl3_1
    | spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f262,f282])).

fof(f262,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl3_4
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f94,plain,(
    v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f42,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f484,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | spl3_2 ),
    inference(forward_demodulation,[],[f474,f64])).

fof(f474,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_1
    | spl3_2 ),
    inference(backward_demodulation,[],[f298,f465])).

fof(f298,plain,
    ( ~ v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0)
    | ~ spl3_1
    | spl3_2 ),
    inference(backward_demodulation,[],[f140,f282])).

fof(f385,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f71,f90,f320,f66])).

fof(f320,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl3_1
    | spl3_2
    | spl3_5 ),
    inference(backward_demodulation,[],[f272,f282])).

fof(f272,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f71,f266,f66])).

fof(f266,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl3_5
  <=> r1_tarski(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f90,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK2(X0,k1_xboole_0)),X0) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | r1_tarski(k2_relat_1(sK2(X0,X1)),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f267,plain,
    ( spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f107,f264,f260])).

fof(f107,plain,
    ( ~ r1_tarski(sK0,k2_relat_1(sK1))
    | sK0 = k2_relat_1(sK1) ),
    inference(resolution,[],[f43,f69])).

fof(f238,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f146,f171,f100,f66])).

fof(f146,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f136,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f136,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f145,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f142,f138,f134])).

fof(f40,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,k1_relat_1(sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:46:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (15211)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (15219)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (15212)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (15221)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (15214)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (15234)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (15213)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (15220)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (15228)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (15210)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (15209)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (15227)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (15237)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (15233)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (15232)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (15235)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (15226)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (15231)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (15229)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (15208)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (15225)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (15236)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (15218)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (15222)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.56  % (15216)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (15217)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (15212)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f544,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f145,f238,f267,f385,f535,f543])).
% 0.22/0.56  fof(f543,plain,(
% 0.22/0.56    spl3_3),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f540])).
% 0.22/0.56  fof(f540,plain,(
% 0.22/0.56    $false | spl3_3),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f42,f144])).
% 0.22/0.56  fof(f144,plain,(
% 0.22/0.56    ~v1_funct_1(sK1) | spl3_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f142])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    spl3_3 <=> v1_funct_1(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    v1_funct_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.56    inference(negated_conjecture,[],[f21])).
% 0.22/0.56  fof(f21,conjecture,(
% 0.22/0.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.22/0.56  fof(f535,plain,(
% 0.22/0.56    ~spl3_1 | spl3_2 | ~spl3_4),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f528])).
% 0.22/0.56  fof(f528,plain,(
% 0.22/0.56    $false | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f484,f488])).
% 0.22/0.56  fof(f488,plain,(
% 0.22/0.56    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.22/0.56    inference(forward_demodulation,[],[f483,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.56  fof(f483,plain,(
% 0.22/0.56    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.22/0.56    inference(backward_demodulation,[],[f388,f465])).
% 0.22/0.56  fof(f465,plain,(
% 0.22/0.56    k1_xboole_0 = sK1 | (~spl3_1 | spl3_2)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f71,f346,f69])).
% 0.22/0.56  fof(f69,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f346,plain,(
% 0.22/0.56    r1_tarski(sK1,k1_xboole_0) | (~spl3_1 | spl3_2)),
% 0.22/0.56    inference(forward_demodulation,[],[f308,f81])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f51])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f308,plain,(
% 0.22/0.56    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k1_xboole_0)) | (~spl3_1 | spl3_2)),
% 0.22/0.56    inference(backward_demodulation,[],[f224,f282])).
% 0.22/0.56  fof(f282,plain,(
% 0.22/0.56    k1_xboole_0 = sK0 | (~spl3_1 | spl3_2)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f140,f135,f254,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.56  fof(f254,plain,(
% 0.22/0.56    k1_relat_1(sK1) = k1_relset_1(k1_relat_1(sK1),sK0,sK1) | ~spl3_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f135,f80])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | ~spl3_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f134])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.56  fof(f140,plain,(
% 0.22/0.56    ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | spl3_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f138])).
% 0.22/0.56  fof(f138,plain,(
% 0.22/0.56    spl3_2 <=> v1_funct_2(sK1,k1_relat_1(sK1),sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.56  fof(f224,plain,(
% 0.22/0.56    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0))),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f171,f100,f66])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(flattening,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k2_zfmisc_1(X0,k2_relat_1(sK1)),k2_zfmisc_1(X0,sK0))) )),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f43,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f171,plain,(
% 0.22/0.56    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f95,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))))),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f41,f42,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    v1_relat_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.56  fof(f388,plain,(
% 0.22/0.56    v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.22/0.56    inference(backward_demodulation,[],[f94,f387])).
% 0.22/0.56  fof(f387,plain,(
% 0.22/0.56    k1_xboole_0 = k2_relat_1(sK1) | (~spl3_1 | spl3_2 | ~spl3_4)),
% 0.22/0.56    inference(forward_demodulation,[],[f262,f282])).
% 0.22/0.56  fof(f262,plain,(
% 0.22/0.56    sK0 = k2_relat_1(sK1) | ~spl3_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f260])).
% 0.22/0.56  fof(f260,plain,(
% 0.22/0.56    spl3_4 <=> sK0 = k2_relat_1(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    v1_funct_2(sK1,k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f41,f42,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f484,plain,(
% 0.22/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_1 | spl3_2)),
% 0.22/0.56    inference(forward_demodulation,[],[f474,f64])).
% 0.22/0.56  fof(f474,plain,(
% 0.22/0.56    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl3_1 | spl3_2)),
% 0.22/0.56    inference(backward_demodulation,[],[f298,f465])).
% 0.22/0.56  fof(f298,plain,(
% 0.22/0.56    ~v1_funct_2(sK1,k1_relat_1(sK1),k1_xboole_0) | (~spl3_1 | spl3_2)),
% 0.22/0.56    inference(backward_demodulation,[],[f140,f282])).
% 0.22/0.56  fof(f385,plain,(
% 0.22/0.56    ~spl3_1 | spl3_2 | spl3_5),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f373])).
% 0.22/0.56  fof(f373,plain,(
% 0.22/0.56    $false | (~spl3_1 | spl3_2 | spl3_5)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f71,f90,f320,f66])).
% 0.22/0.56  fof(f320,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl3_1 | spl3_2 | spl3_5)),
% 0.22/0.56    inference(backward_demodulation,[],[f272,f282])).
% 0.22/0.56  fof(f272,plain,(
% 0.22/0.56    ~r1_tarski(sK0,k1_xboole_0) | spl3_5),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f71,f266,f66])).
% 0.22/0.56  fof(f266,plain,(
% 0.22/0.56    ~r1_tarski(sK0,k2_relat_1(sK1)) | spl3_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f264])).
% 0.22/0.56  fof(f264,plain,(
% 0.22/0.56    spl3_5 <=> r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(sK2(X0,k1_xboole_0)),X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | r1_tarski(k2_relat_1(sK2(X0,X1)),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1] : (? [X2] : (r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1 & v1_funct_1(X2) & v1_relat_1(X2)) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.56    inference(flattening,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1] : (? [X2] : ((r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1) & (v1_funct_1(X2) & v1_relat_1(X2))) | (k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 0.22/0.56  fof(f267,plain,(
% 0.22/0.56    spl3_4 | ~spl3_5),
% 0.22/0.56    inference(avatar_split_clause,[],[f107,f264,f260])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ~r1_tarski(sK0,k2_relat_1(sK1)) | sK0 = k2_relat_1(sK1)),
% 0.22/0.56    inference(resolution,[],[f43,f69])).
% 0.22/0.56  fof(f238,plain,(
% 0.22/0.56    spl3_1),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f225])).
% 0.22/0.56  fof(f225,plain,(
% 0.22/0.56    $false | spl3_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f146,f171,f100,f66])).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    ~r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),sK0)) | spl3_1),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f136,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f136,plain,(
% 0.22/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0))) | spl3_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f134])).
% 0.22/0.56  fof(f145,plain,(
% 0.22/0.56    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.22/0.56    inference(avatar_split_clause,[],[f40,f142,f138,f134])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,k1_relat_1(sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK1),sK0)))),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (15212)------------------------------
% 0.22/0.56  % (15212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15212)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (15212)Memory used [KB]: 6396
% 0.22/0.56  % (15212)Time elapsed: 0.134 s
% 0.22/0.56  % (15212)------------------------------
% 0.22/0.56  % (15212)------------------------------
% 0.22/0.56  % (15207)Success in time 0.2 s
%------------------------------------------------------------------------------
