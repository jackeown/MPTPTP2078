%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0836+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:44 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 132 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :  193 ( 424 expanded)
%              Number of equality atoms :    6 (  20 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f56,f72,f85,f114,f118,f121,f139])).

fof(f139,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f137,f122])).

fof(f122,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f86,f22])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <~> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relset_1)).

fof(f86,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_1 ),
    inference(superposition,[],[f42,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f42,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl8_1
  <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f137,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f136,f125])).

fof(f125,plain,
    ( ~ r2_hidden(sK6(sK2,sK3),sK1)
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(resolution,[],[f123,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f123,plain,
    ( ~ m1_subset_1(sK6(sK2,sK3),sK1)
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f88,f122])).

fof(f88,plain,
    ( ~ m1_subset_1(sK6(sK2,sK3),sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_4 ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f55,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl8_4
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f136,plain,
    ( ! [X1] :
        ( r2_hidden(sK6(sK2,X1),sK1)
        | ~ r2_hidden(X1,k1_relat_1(sK2)) )
    | ~ spl8_9 ),
    inference(resolution,[],[f127,f37])).

fof(f127,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
        | r2_hidden(X3,sK1) )
    | ~ spl8_9 ),
    inference(resolution,[],[f113,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f113,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_9
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f121,plain,
    ( ~ spl8_1
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f119,f22])).

fof(f119,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f86,f117])).

fof(f117,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_relat_1(sK2))
    | ~ spl8_6 ),
    inference(resolution,[],[f71,f37])).

fof(f71,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl8_6
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f118,plain,
    ( ~ spl8_2
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(resolution,[],[f71,f46])).

fof(f46,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl8_2
  <=> r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f114,plain,
    ( spl8_5
    | spl8_9 ),
    inference(avatar_split_clause,[],[f94,f112,f66])).

fof(f66,plain,
    ( spl8_5
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f63,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f63,plain,(
    ! [X1] :
      ( m1_subset_1(X1,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f85,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f83,f22])).

fof(f83,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f82,f61])).

fof(f61,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl8_2 ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f82,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_1 ),
    inference(superposition,[],[f41,f31])).

fof(f41,plain,
    ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f72,plain,
    ( ~ spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f62,f70,f66])).

fof(f62,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f22,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f56,plain,
    ( ~ spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f18,f54,f40])).

fof(f18,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f20,f44,f40])).

fof(f20,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

%------------------------------------------------------------------------------
