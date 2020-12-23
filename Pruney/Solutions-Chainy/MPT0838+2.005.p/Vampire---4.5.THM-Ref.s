%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 376 expanded)
%              Number of leaves         :   30 ( 114 expanded)
%              Depth                    :   12
%              Number of atoms          :  362 (1059 expanded)
%              Number of equality atoms :   30 ( 143 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f130,f142,f147,f152,f190,f284,f400,f413,f454,f511,f547,f571,f572,f591,f605,f656])).

fof(f656,plain,
    ( ~ spl4_28
    | ~ spl4_21
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f653,f491,f119,f409,f566])).

fof(f566,plain,
    ( spl4_28
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f409,plain,
    ( spl4_21
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f119,plain,
    ( spl4_5
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f491,plain,
    ( spl4_27
  <=> ! [X3] :
        ( ~ r1_tarski(k2_relat_1(sK2),X3)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f653,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(superposition,[],[f648,f606])).

fof(f606,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f578,f580])).

fof(f580,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f120,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f120,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f578,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k2_relat_1(sK2))
    | ~ spl4_5 ),
    inference(resolution,[],[f120,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f47,f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f648,plain,
    ( ! [X3] :
        ( ~ v1_xboole_0(k2_zfmisc_1(sK0,X3))
        | ~ r1_tarski(k1_xboole_0,X3) )
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f492,f580])).

fof(f492,plain,
    ( ! [X3] :
        ( ~ r1_tarski(k2_relat_1(sK2),X3)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,X3)) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f491])).

fof(f605,plain,
    ( ~ spl4_13
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f604])).

fof(f604,plain,
    ( $false
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(resolution,[],[f600,f548])).

fof(f548,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_13 ),
    inference(resolution,[],[f189,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f189,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_13
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f600,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_18 ),
    inference(resolution,[],[f563,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f49,f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f40,f39])).

fof(f39,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f563,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_18 ),
    inference(resolution,[],[f399,f47])).

fof(f399,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_zfmisc_1(sK0,X0))
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl4_18
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f591,plain,
    ( ~ spl4_9
    | spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f587,f119,f164,f140])).

fof(f140,plain,
    ( spl4_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f164,plain,
    ( spl4_10
  <=> ! [X0] :
        ( r1_tarski(k1_xboole_0,X0)
        | ~ v5_relat_1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f587,plain,
    ( ! [X13] :
        ( r1_tarski(k1_xboole_0,X13)
        | ~ v1_relat_1(sK2)
        | ~ v5_relat_1(sK2,X13) )
    | ~ spl4_5 ),
    inference(superposition,[],[f46,f580])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f572,plain,
    ( spl4_4
    | spl4_27 ),
    inference(avatar_split_clause,[],[f386,f491,f91])).

fof(f91,plain,
    ( spl4_4
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f386,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ r2_hidden(X1,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,X0)) ) ),
    inference(resolution,[],[f113,f35])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

fof(f113,plain,(
    ! [X19,X17,X20,X18,X16] :
      ( ~ r1_tarski(k2_relat_1(X16),X17)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | ~ r2_hidden(X20,X16)
      | ~ v1_xboole_0(k2_zfmisc_1(X18,X17)) ) ),
    inference(resolution,[],[f56,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f571,plain,(
    spl4_28 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | spl4_28 ),
    inference(resolution,[],[f567,f72])).

fof(f567,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_28 ),
    inference(avatar_component_clause,[],[f566])).

fof(f547,plain,
    ( ~ spl4_12
    | spl4_13
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f546,f65,f188,f185])).

fof(f185,plain,
    ( spl4_12
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f65,plain,
    ( spl4_2
  <=> v1_xboole_0(k2_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f546,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) )
    | ~ spl4_2 ),
    inference(factoring,[],[f497])).

fof(f497,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_2 ),
    inference(resolution,[],[f327,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f327,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | ~ r2_hidden(X3,k1_xboole_0) )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f116,f315])).

fof(f315,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f312,f41])).

fof(f312,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f66,f105])).

fof(f105,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f52,f35])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f66,plain,
    ( v1_xboole_0(k2_relset_1(sK0,sK1,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f116,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(backward_demodulation,[],[f34,f105])).

fof(f34,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f511,plain,
    ( ~ spl4_9
    | spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f507,f65,f164,f140])).

fof(f507,plain,
    ( ! [X13] :
        ( r1_tarski(k1_xboole_0,X13)
        | ~ v1_relat_1(sK2)
        | ~ v5_relat_1(sK2,X13) )
    | ~ spl4_2 ),
    inference(superposition,[],[f46,f315])).

fof(f454,plain,
    ( ~ spl4_4
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(trivial_inequality_removal,[],[f452])).

fof(f452,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(superposition,[],[f426,f288])).

fof(f288,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_13 ),
    inference(resolution,[],[f266,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f42,f41])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f266,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_13 ),
    inference(resolution,[],[f189,f43])).

fof(f426,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f104,f417])).

fof(f417,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_4 ),
    inference(resolution,[],[f414,f41])).

fof(f414,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f92,f43])).

fof(f92,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f104,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(superposition,[],[f36,f100])).

fof(f100,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f51,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f36,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f413,plain,
    ( ~ spl4_13
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl4_13
    | spl4_21 ),
    inference(resolution,[],[f410,f266])).

fof(f410,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f409])).

fof(f400,plain,
    ( spl4_4
    | spl4_18
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f396,f65,f398,f91])).

fof(f396,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ r2_hidden(X1,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,X0)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f386,f315])).

fof(f284,plain,
    ( ~ spl4_10
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | ~ spl4_10
    | spl4_12 ),
    inference(resolution,[],[f254,f80])).

fof(f80,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f53,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f254,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ spl4_10
    | spl4_12 ),
    inference(resolution,[],[f165,f191])).

% (1425)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f191,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl4_12 ),
    inference(resolution,[],[f186,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f186,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f185])).

fof(f165,plain,
    ( ! [X0] :
        ( r1_tarski(k1_xboole_0,X0)
        | ~ v5_relat_1(sK2,X0) )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f164])).

fof(f190,plain,
    ( ~ spl4_12
    | spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f183,f119,f188,f185])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) )
    | ~ spl4_5 ),
    inference(factoring,[],[f171])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_5 ),
    inference(resolution,[],[f159,f54])).

fof(f159,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | ~ r2_hidden(X3,k1_xboole_0) )
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f116,f155])).

fof(f155,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl4_5 ),
    inference(resolution,[],[f120,f41])).

fof(f152,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f138,f80])).

fof(f138,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl4_8
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f147,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl4_9 ),
    inference(resolution,[],[f141,f74])).

fof(f74,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f50,f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f141,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_7 ),
    inference(avatar_split_clause,[],[f135,f128,f140,f137])).

fof(f128,plain,
    ( spl4_7
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f135,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK1)
    | spl4_7 ),
    inference(resolution,[],[f131,f46])).

fof(f131,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl4_7 ),
    inference(resolution,[],[f129,f48])).

fof(f129,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f128])).

fof(f130,plain,
    ( spl4_5
    | ~ spl4_7
    | spl4_1 ),
    inference(avatar_split_clause,[],[f126,f62,f128,f119])).

fof(f62,plain,
    ( spl4_1
  <=> m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f126,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | v1_xboole_0(k2_relat_1(sK2))
    | spl4_1 ),
    inference(resolution,[],[f125,f43])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_relat_1(sK2)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | spl4_1 ),
    inference(resolution,[],[f115,f54])).

fof(f115,plain,
    ( ~ m1_subset_1(sK3(k2_relat_1(sK2)),sK1)
    | spl4_1 ),
    inference(backward_demodulation,[],[f63,f105])).

fof(f63,plain,
    ( ~ m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f67,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f59,f65,f62])).

fof(f59,plain,
    ( v1_xboole_0(k2_relset_1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1) ),
    inference(resolution,[],[f43,f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:49:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (1434)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (1442)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.49  % (1442)Refutation not found, incomplete strategy% (1442)------------------------------
% 0.21/0.49  % (1442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1442)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (1442)Memory used [KB]: 6140
% 0.21/0.49  % (1442)Time elapsed: 0.071 s
% 0.21/0.49  % (1442)------------------------------
% 0.21/0.49  % (1442)------------------------------
% 0.21/0.49  % (1424)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (1434)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f657,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f67,f130,f142,f147,f152,f190,f284,f400,f413,f454,f511,f547,f571,f572,f591,f605,f656])).
% 0.21/0.49  fof(f656,plain,(
% 0.21/0.49    ~spl4_28 | ~spl4_21 | ~spl4_5 | ~spl4_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f653,f491,f119,f409,f566])).
% 0.21/0.49  fof(f566,plain,(
% 0.21/0.49    spl4_28 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.49  fof(f409,plain,(
% 0.21/0.49    spl4_21 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl4_5 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f491,plain,(
% 0.21/0.49    spl4_27 <=> ! [X3] : (~r1_tarski(k2_relat_1(sK2),X3) | ~v1_xboole_0(k2_zfmisc_1(sK0,X3)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.49  fof(f653,plain,(
% 0.21/0.49    ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl4_5 | ~spl4_27)),
% 0.21/0.49    inference(superposition,[],[f648,f606])).
% 0.21/0.49  fof(f606,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl4_5),
% 0.21/0.49    inference(forward_demodulation,[],[f578,f580])).
% 0.21/0.49  fof(f580,plain,(
% 0.21/0.49    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f120,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    v1_xboole_0(k2_relat_1(sK2)) | ~spl4_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f578,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k2_relat_1(sK2))) ) | ~spl4_5),
% 0.21/0.50    inference(resolution,[],[f120,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f47,f41])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.21/0.50  fof(f648,plain,(
% 0.21/0.50    ( ! [X3] : (~v1_xboole_0(k2_zfmisc_1(sK0,X3)) | ~r1_tarski(k1_xboole_0,X3)) ) | (~spl4_5 | ~spl4_27)),
% 0.21/0.50    inference(forward_demodulation,[],[f492,f580])).
% 0.21/0.50  fof(f492,plain,(
% 0.21/0.50    ( ! [X3] : (~r1_tarski(k2_relat_1(sK2),X3) | ~v1_xboole_0(k2_zfmisc_1(sK0,X3))) ) | ~spl4_27),
% 0.21/0.50    inference(avatar_component_clause,[],[f491])).
% 0.21/0.50  fof(f605,plain,(
% 0.21/0.50    ~spl4_13 | ~spl4_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f604])).
% 0.21/0.50  fof(f604,plain,(
% 0.21/0.50    $false | (~spl4_13 | ~spl4_18)),
% 0.21/0.50    inference(resolution,[],[f600,f548])).
% 0.21/0.50  fof(f548,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0) | ~spl4_13),
% 0.21/0.50    inference(resolution,[],[f189,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f188])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    spl4_13 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.50  fof(f600,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | ~spl4_18),
% 0.21/0.50    inference(resolution,[],[f563,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.50    inference(resolution,[],[f49,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f40,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f563,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_xboole_0(X0)) ) | ~spl4_18),
% 0.21/0.50    inference(resolution,[],[f399,f47])).
% 0.21/0.50  fof(f399,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(sK0,X0)) | ~r1_tarski(k1_xboole_0,X0)) ) | ~spl4_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f398])).
% 0.21/0.50  fof(f398,plain,(
% 0.21/0.50    spl4_18 <=> ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_xboole_0(k2_zfmisc_1(sK0,X0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.50  fof(f591,plain,(
% 0.21/0.50    ~spl4_9 | spl4_10 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f587,f119,f164,f140])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl4_9 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    spl4_10 <=> ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~v5_relat_1(sK2,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.50  fof(f587,plain,(
% 0.21/0.50    ( ! [X13] : (r1_tarski(k1_xboole_0,X13) | ~v1_relat_1(sK2) | ~v5_relat_1(sK2,X13)) ) | ~spl4_5),
% 0.21/0.50    inference(superposition,[],[f46,f580])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.50  fof(f572,plain,(
% 0.21/0.50    spl4_4 | spl4_27),
% 0.21/0.50    inference(avatar_split_clause,[],[f386,f491,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl4_4 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(sK2),X0) | ~r2_hidden(X1,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,X0))) )),
% 0.21/0.50    inference(resolution,[],[f113,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f16])).
% 0.21/0.50  fof(f16,conjecture,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ( ! [X19,X17,X20,X18,X16] : (~r1_tarski(k2_relat_1(X16),X17) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | ~r2_hidden(X20,X16) | ~v1_xboole_0(k2_zfmisc_1(X18,X17))) )),
% 0.21/0.50    inference(resolution,[],[f56,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 0.21/0.50  fof(f571,plain,(
% 0.21/0.50    spl4_28),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f569])).
% 0.21/0.50  fof(f569,plain,(
% 0.21/0.50    $false | spl4_28),
% 0.21/0.50    inference(resolution,[],[f567,f72])).
% 0.21/0.50  fof(f567,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f566])).
% 0.21/0.50  fof(f547,plain,(
% 0.21/0.50    ~spl4_12 | spl4_13 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f546,f65,f188,f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    spl4_12 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl4_2 <=> v1_xboole_0(k2_relset_1(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f546,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))) ) | ~spl4_2),
% 0.21/0.50    inference(factoring,[],[f497])).
% 0.21/0.50  fof(f497,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,X1)) ) | ~spl4_2),
% 0.21/0.50    inference(resolution,[],[f327,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f327,plain,(
% 0.21/0.50    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_xboole_0)) ) | ~spl4_2),
% 0.21/0.50    inference(backward_demodulation,[],[f116,f315])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_2),
% 0.21/0.50    inference(resolution,[],[f312,f41])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    v1_xboole_0(k2_relat_1(sK2)) | ~spl4_2),
% 0.21/0.50    inference(backward_demodulation,[],[f66,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f52,f35])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    v1_xboole_0(k2_relset_1(sK0,sK1,sK2)) | ~spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f65])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(X3,k2_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.50    inference(backward_demodulation,[],[f34,f105])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f511,plain,(
% 0.21/0.50    ~spl4_9 | spl4_10 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f507,f65,f164,f140])).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    ( ! [X13] : (r1_tarski(k1_xboole_0,X13) | ~v1_relat_1(sK2) | ~v5_relat_1(sK2,X13)) ) | ~spl4_2),
% 0.21/0.50    inference(superposition,[],[f46,f315])).
% 0.21/0.50  fof(f454,plain,(
% 0.21/0.50    ~spl4_4 | ~spl4_13),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f453])).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    $false | (~spl4_4 | ~spl4_13)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f452])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    k1_xboole_0 != k1_xboole_0 | (~spl4_4 | ~spl4_13)),
% 0.21/0.50    inference(superposition,[],[f426,f288])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_13),
% 0.21/0.50    inference(resolution,[],[f266,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f42,f41])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0) | ~spl4_13),
% 0.21/0.50    inference(resolution,[],[f189,f43])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~spl4_4),
% 0.21/0.50    inference(backward_demodulation,[],[f104,f417])).
% 0.21/0.50  fof(f417,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~spl4_4),
% 0.21/0.50    inference(resolution,[],[f414,f41])).
% 0.21/0.50  fof(f414,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | ~spl4_4),
% 0.21/0.50    inference(resolution,[],[f92,f43])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f91])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(sK2)),
% 0.21/0.50    inference(superposition,[],[f36,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f51,f35])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    ~spl4_13 | spl4_21),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f412])).
% 0.21/0.50  fof(f412,plain,(
% 0.21/0.50    $false | (~spl4_13 | spl4_21)),
% 0.21/0.50    inference(resolution,[],[f410,f266])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    ~v1_xboole_0(k1_xboole_0) | spl4_21),
% 0.21/0.50    inference(avatar_component_clause,[],[f409])).
% 0.21/0.50  fof(f400,plain,(
% 0.21/0.50    spl4_4 | spl4_18 | ~spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f396,f65,f398,f91])).
% 0.21/0.50  fof(f396,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~r2_hidden(X1,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,X0))) ) | ~spl4_2),
% 0.21/0.50    inference(forward_demodulation,[],[f386,f315])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    ~spl4_10 | spl4_12),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f282])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    $false | (~spl4_10 | spl4_12)),
% 0.21/0.50    inference(resolution,[],[f254,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    v5_relat_1(sK2,sK1)),
% 0.21/0.50    inference(resolution,[],[f53,f35])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ~v5_relat_1(sK2,sK1) | (~spl4_10 | spl4_12)),
% 0.21/0.50    inference(resolution,[],[f165,f191])).
% 0.21/0.50  % (1425)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ~r1_tarski(k1_xboole_0,sK1) | spl4_12),
% 0.21/0.50    inference(resolution,[],[f186,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | spl4_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f185])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~v5_relat_1(sK2,X0)) ) | ~spl4_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f164])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ~spl4_12 | spl4_13 | ~spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f183,f119,f188,f185])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))) ) | ~spl4_5),
% 0.21/0.50    inference(factoring,[],[f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(sK1)) | ~r2_hidden(X0,X1)) ) | ~spl4_5),
% 0.21/0.50    inference(resolution,[],[f159,f54])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_xboole_0)) ) | ~spl4_5),
% 0.21/0.50    inference(backward_demodulation,[],[f116,f155])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~spl4_5),
% 0.21/0.50    inference(resolution,[],[f120,f41])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    spl4_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    $false | spl4_8),
% 0.21/0.50    inference(resolution,[],[f138,f80])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~v5_relat_1(sK2,sK1) | spl4_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f137])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl4_8 <=> v5_relat_1(sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl4_9),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f146])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    $false | spl4_9),
% 0.21/0.50    inference(resolution,[],[f141,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f50,f35])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | spl4_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f140])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~spl4_8 | ~spl4_9 | spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f135,f128,f140,f137])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    spl4_7 <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | ~v5_relat_1(sK2,sK1) | spl4_7),
% 0.21/0.50    inference(resolution,[],[f131,f46])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ~r1_tarski(k2_relat_1(sK2),sK1) | spl4_7),
% 0.21/0.50    inference(resolution,[],[f129,f48])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | spl4_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f128])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    spl4_5 | ~spl4_7 | spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f126,f62,f128,f119])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl4_1 <=> m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ~m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) | v1_xboole_0(k2_relat_1(sK2)) | spl4_1),
% 0.21/0.50    inference(resolution,[],[f125,f43])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK3(k2_relat_1(sK2)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) ) | spl4_1),
% 0.21/0.50    inference(resolution,[],[f115,f54])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ~m1_subset_1(sK3(k2_relat_1(sK2)),sK1) | spl4_1),
% 0.21/0.50    inference(backward_demodulation,[],[f63,f105])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ~m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ~spl4_1 | spl4_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f65,f62])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    v1_xboole_0(k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(sK3(k2_relset_1(sK0,sK1,sK2)),sK1)),
% 0.21/0.50    inference(resolution,[],[f43,f34])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1434)------------------------------
% 0.21/0.50  % (1434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1434)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1434)Memory used [KB]: 10874
% 0.21/0.50  % (1434)Time elapsed: 0.081 s
% 0.21/0.50  % (1434)------------------------------
% 0.21/0.50  % (1434)------------------------------
% 0.21/0.50  % (1425)Refutation not found, incomplete strategy% (1425)------------------------------
% 0.21/0.50  % (1425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1425)Memory used [KB]: 10618
% 0.21/0.50  % (1425)Time elapsed: 0.095 s
% 0.21/0.50  % (1425)------------------------------
% 0.21/0.50  % (1425)------------------------------
% 0.21/0.50  % (1421)Success in time 0.141 s
%------------------------------------------------------------------------------
