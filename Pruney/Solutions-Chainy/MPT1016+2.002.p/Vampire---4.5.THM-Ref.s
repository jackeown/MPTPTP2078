%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  165 (106087 expanded)
%              Number of leaves         :   11 (21564 expanded)
%              Depth                    :   77
%              Number of atoms          :  665 (513333 expanded)
%              Number of equality atoms :  306 (125412 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f747,plain,(
    $false ),
    inference(subsumption_resolution,[],[f675,f733])).

fof(f733,plain,(
    ~ v4_relat_1(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f131,f728])).

fof(f728,plain,(
    ~ v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f668,f81])).

fof(f81,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f80,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f79,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f668,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ v2_funct_1(sK1) ),
    inference(backward_demodulation,[],[f24,f667])).

fof(f667,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f666,f607])).

fof(f607,plain,
    ( ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f594])).

fof(f594,plain,
    ( sK2 != sK2
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f27,f590])).

fof(f590,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f581])).

fof(f581,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | sK2 = sK3
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(superposition,[],[f578,f558])).

fof(f558,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f542,f454])).

fof(f454,plain,
    ( v2_funct_1(sK1)
    | sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f453,f55])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f453,plain,
    ( ~ v1_relat_1(sK1)
    | v2_funct_1(sK1)
    | sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f452,f29])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f452,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1)
    | sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f450])).

fof(f450,plain,
    ( sK4(sK1) != sK4(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1)
    | sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f37,f444])).

fof(f444,plain,
    ( sK4(sK1) = sK5(sK1)
    | sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f435])).

fof(f435,plain,
    ( sK2 = sK3
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(superposition,[],[f434,f423])).

fof(f423,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f411,f371])).

fof(f371,plain,
    ( v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f370,f51])).

fof(f370,plain,
    ( sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3
    | ~ r1_tarski(sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f367])).

fof(f367,plain,
    ( sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3
    | ~ r1_tarski(sK0,sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f366,f136])).

fof(f136,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK1),X1)
      | ~ r1_tarski(sK0,X1)
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f133,f69])).

fof(f69,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(resolution,[],[f47,f31])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(sK1,X1)
      | r2_hidden(sK4(sK1),X0)
      | ~ r1_tarski(X1,X0)
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f129,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(sK1),X0)
      | ~ v4_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f39,f55])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | v2_funct_1(sK1)
      | r2_hidden(sK4(sK1),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f127,f84])).

fof(f84,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X1,X2)
      | r2_hidden(X1,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f40,f44])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f127,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1),X0)
      | v2_funct_1(sK1)
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(subsumption_resolution,[],[f126,f55])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | v2_funct_1(sK1)
      | r2_hidden(sK4(sK1),X0)
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f92,f29])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0)
      | r2_hidden(sK4(X0),X1)
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(resolution,[],[f34,f84])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

% (14410)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f366,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(duplicate_literal_removal,[],[f365])).

fof(f365,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3
    | sK4(sK1) = sK5(sK1) ),
    inference(equality_resolution,[],[f362])).

fof(f362,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | sK2 = sK3
      | sK4(sK1) = sK5(sK1) ) ),
    inference(subsumption_resolution,[],[f361,f51])).

fof(f361,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | sK2 = sK3
      | sK4(sK1) = sK5(sK1)
      | ~ r1_tarski(sK0,sK0) ) ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | sK2 = sK3
      | sK4(sK1) = sK5(sK1)
      | ~ r1_tarski(sK0,sK0)
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f347,f151])).

fof(f151,plain,(
    ! [X1] :
      ( r2_hidden(sK5(sK1),X1)
      | ~ r1_tarski(sK0,X1)
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f148,f69])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(sK1,X1)
      | r2_hidden(sK5(sK1),X0)
      | ~ r1_tarski(X1,X0)
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f146,f62])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK1),X0)
      | v2_funct_1(sK1)
      | r2_hidden(sK5(sK1),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f144,f84])).

fof(f144,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK1),X0)
      | v2_funct_1(sK1)
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(subsumption_resolution,[],[f143,f55])).

fof(f143,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | v2_funct_1(sK1)
      | r2_hidden(sK5(sK1),X0)
      | ~ r1_tarski(k1_relat_1(sK1),X0) ) ),
    inference(resolution,[],[f93,f29])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0)
      | r2_hidden(sK5(X0),X1)
      | ~ r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(resolution,[],[f35,f84])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f347,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK1),sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | v2_funct_1(sK1)
      | k1_xboole_0 = sK0
      | sK2 = sK3
      | sK4(sK1) = sK5(sK1) ) ),
    inference(superposition,[],[f28,f344])).

fof(f344,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | k1_xboole_0 = sK0
    | sK2 = sK3
    | sK4(sK1) = sK5(sK1) ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(superposition,[],[f312,f306])).

fof(f306,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(subsumption_resolution,[],[f305,f51])).

fof(f305,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ r1_tarski(sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ r1_tarski(sK0,sK0)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(resolution,[],[f295,f101])).

fof(f101,plain,(
    ! [X1] :
      ( r2_hidden(sK2,X1)
      | ~ r1_tarski(sK0,X1)
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ) ),
    inference(subsumption_resolution,[],[f100,f55])).

fof(f100,plain,(
    ! [X1] :
      ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(sK0,X1)
      | r2_hidden(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f96,f29])).

fof(f96,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK1)
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(sK0,X1)
      | r2_hidden(sK2,X1) ) ),
    inference(resolution,[],[f36,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_funct_1(sK1)
      | ~ r1_tarski(sK0,X0)
      | r2_hidden(sK2,X0) ) ),
    inference(resolution,[],[f84,f24])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f295,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ) ),
    inference(subsumption_resolution,[],[f293,f30])).

fof(f30,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f293,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK1,sK0,sK0)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ) ),
    inference(resolution,[],[f292,f31])).

fof(f292,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK1,X0,X1)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ) ),
    inference(resolution,[],[f246,f29])).

fof(f246,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X2
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) ) ),
    inference(subsumption_resolution,[],[f245,f46])).

fof(f245,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X2
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f238])).

fof(f238,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,X1)
      | k1_xboole_0 = X2
      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f50,f36])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f312,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1) ),
    inference(superposition,[],[f307,f222])).

fof(f222,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f221,f26])).

fof(f26,plain,
    ( ~ v2_funct_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f221,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f219,f51])).

fof(f219,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ r1_tarski(sK0,sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f218,f136])).

fof(f218,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | sK4(sK1) = sK5(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(equality_resolution,[],[f216])).

fof(f216,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ) ),
    inference(subsumption_resolution,[],[f215,f26])).

fof(f215,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      | v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f213,f51])).

fof(f213,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      | ~ r1_tarski(sK0,sK0)
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f158,f151])).

fof(f158,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK1),sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ) ),
    inference(subsumption_resolution,[],[f156,f26])).

fof(f156,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(sK5(sK1),sK0)
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | v2_funct_1(sK1)
      | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ) ),
    inference(superposition,[],[f28,f103])).

fof(f103,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f102,f55])).

fof(f102,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f97,f29])).

fof(f97,plain,
    ( ~ v1_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(resolution,[],[f36,f26])).

fof(f307,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(subsumption_resolution,[],[f304,f51])).

fof(f304,plain,
    ( k1_xboole_0 = sK0
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ r1_tarski(sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( k1_xboole_0 = sK0
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ r1_tarski(sK0,sK0)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(resolution,[],[f295,f99])).

fof(f99,plain,(
    ! [X0] :
      ( r2_hidden(sK3,X0)
      | ~ r1_tarski(sK0,X0)
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ) ),
    inference(subsumption_resolution,[],[f98,f55])).

fof(f98,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(sK0,X0)
      | r2_hidden(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f95,f29])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK1)
      | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
      | ~ v1_relat_1(sK1)
      | ~ r1_tarski(sK0,X0)
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f36,f86])).

fof(f86,plain,(
    ! [X1] :
      ( ~ v2_funct_1(sK1)
      | ~ r1_tarski(sK0,X1)
      | r2_hidden(sK3,X1) ) ),
    inference(resolution,[],[f84,f25])).

fof(f25,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X2,sK0)
      | X2 = X3
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f411,plain,
    ( sK2 = sK3
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f410,f24])).

fof(f410,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK2 = sK3
      | sK4(sK1) = sK5(sK1)
      | k1_xboole_0 = sK0
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f409,f30])).

fof(f409,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | sK2 = sK3
      | ~ v1_funct_2(sK1,sK0,sK0)
      | sK4(sK1) = sK5(sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f407])).

fof(f407,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | sK2 = sK3
      | ~ v1_funct_2(sK1,sK0,sK0)
      | sK4(sK1) = sK5(sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f380,f31])).

fof(f380,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK0
      | sK2 = sK3
      | ~ v1_funct_2(sK1,X2,X3)
      | sK4(sK1) = sK5(sK1)
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X3
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X4)) = X4 ) ),
    inference(subsumption_resolution,[],[f377,f29])).

fof(f377,plain,(
    ! [X4,X2,X3] :
      ( sK4(sK1) = sK5(sK1)
      | k1_xboole_0 = sK0
      | sK2 = sK3
      | ~ v1_funct_2(sK1,X2,X3)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X3
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X4)) = X4 ) ),
    inference(resolution,[],[f371,f50])).

fof(f434,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(duplicate_literal_removal,[],[f431])).

fof(f431,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3
    | sK4(sK1) = sK5(sK1) ),
    inference(superposition,[],[f424,f222])).

fof(f424,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f412,f371])).

fof(f412,plain,
    ( sK2 = sK3
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f410,f25])).

fof(f37,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f542,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f541,f24])).

fof(f541,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | sK2 = sK3
      | k1_xboole_0 = sK0
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f540,f30])).

fof(f540,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ v1_funct_2(sK1,sK0,sK0)
      | sK2 = sK3
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f538])).

fof(f538,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | ~ v1_funct_2(sK1,sK0,sK0)
      | sK2 = sK3
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK0
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    inference(resolution,[],[f463,f31])).

fof(f463,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_xboole_0 = sK0
      | ~ v1_funct_2(sK1,X2,X3)
      | sK2 = sK3
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X3
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X4)) = X4 ) ),
    inference(subsumption_resolution,[],[f460,f29])).

fof(f460,plain,(
    ! [X4,X2,X3] :
      ( sK2 = sK3
      | k1_xboole_0 = sK0
      | ~ v1_funct_2(sK1,X2,X3)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(sK1)
      | ~ r2_hidden(X4,X2)
      | k1_xboole_0 = X3
      | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X4)) = X4 ) ),
    inference(resolution,[],[f454,f50])).

fof(f578,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(duplicate_literal_removal,[],[f574])).

fof(f574,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | sK2 = sK3
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(superposition,[],[f559,f459])).

fof(f459,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(resolution,[],[f454,f26])).

fof(f559,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f543,f454])).

fof(f543,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f541,f25])).

fof(f27,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f666,plain,
    ( v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f665,f55])).

fof(f665,plain,
    ( ~ v1_relat_1(sK1)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f662,f29])).

fof(f662,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f660])).

fof(f660,plain,
    ( sK4(sK1) != sK4(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | v2_funct_1(sK1)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f37,f651])).

fof(f651,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f650,f607])).

fof(f650,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f648,f51])).

fof(f648,plain,
    ( sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0
    | ~ r1_tarski(sK0,sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f647,f136])).

fof(f647,plain,
    ( ~ r2_hidden(sK4(sK1),sK0)
    | sK4(sK1) = sK5(sK1)
    | k1_xboole_0 = sK0 ),
    inference(equality_resolution,[],[f642])).

fof(f642,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f641,f607])).

fof(f641,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | k1_xboole_0 = sK0
      | v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f637,f51])).

fof(f637,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | k1_xboole_0 = sK0
      | ~ r1_tarski(sK0,sK0)
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f627,f151])).

fof(f627,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(sK1),sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f623,f607])).

fof(f623,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | ~ r2_hidden(sK5(sK1),sK0)
      | ~ r2_hidden(X0,sK0)
      | sK5(sK1) = X0
      | v2_funct_1(sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f28,f619])).

fof(f619,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f618,f55])).

fof(f618,plain,
    ( k1_xboole_0 = sK0
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f613,f29])).

fof(f613,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f607,f36])).

fof(f24,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f131,plain,
    ( ~ v4_relat_1(sK1,k1_xboole_0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f128,f62])).

fof(f128,plain,
    ( ~ r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f127,f81])).

fof(f675,plain,(
    v4_relat_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f69,f667])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (14417)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.46  % (14413)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.47  % (14409)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.47  % (14413)Refutation not found, incomplete strategy% (14413)------------------------------
% 0.21/0.47  % (14413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14421)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.47  % (14413)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (14413)Memory used [KB]: 10618
% 0.21/0.47  % (14413)Time elapsed: 0.063 s
% 0.21/0.47  % (14413)------------------------------
% 0.21/0.47  % (14413)------------------------------
% 0.21/0.50  % (14425)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (14426)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.50  % (14421)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f747,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f675,f733])).
% 0.21/0.50  fof(f733,plain,(
% 0.21/0.50    ~v4_relat_1(sK1,k1_xboole_0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f131,f728])).
% 0.21/0.50  fof(f728,plain,(
% 0.21/0.50    ~v2_funct_1(sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f668,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f80,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f79,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f49,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.50  fof(f668,plain,(
% 0.21/0.50    r2_hidden(sK2,k1_xboole_0) | ~v2_funct_1(sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f24,f667])).
% 0.21/0.50  fof(f667,plain,(
% 0.21/0.50    k1_xboole_0 = sK0),
% 0.21/0.50    inference(subsumption_resolution,[],[f666,f607])).
% 0.21/0.50  fof(f607,plain,(
% 0.21/0.50    ~v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f594])).
% 0.21/0.50  fof(f594,plain,(
% 0.21/0.50    sK2 != sK2 | ~v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.50    inference(superposition,[],[f27,f590])).
% 0.21/0.50  fof(f590,plain,(
% 0.21/0.50    sK2 = sK3 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f581])).
% 0.21/0.50  fof(f581,plain,(
% 0.21/0.50    sK2 = sK3 | k1_xboole_0 = sK0 | sK2 = sK3 | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.50    inference(superposition,[],[f578,f558])).
% 0.21/0.50  fof(f558,plain,(
% 0.21/0.50    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.50    inference(subsumption_resolution,[],[f542,f454])).
% 0.21/0.50  fof(f454,plain,(
% 0.21/0.50    v2_funct_1(sK1) | sK2 = sK3 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(subsumption_resolution,[],[f453,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(resolution,[],[f46,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.50    inference(negated_conjecture,[],[f11])).
% 0.21/0.50  fof(f11,conjecture,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_funct_2)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | v2_funct_1(sK1) | sK2 = sK3 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(subsumption_resolution,[],[f452,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    v1_funct_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | v2_funct_1(sK1) | sK2 = sK3 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f450])).
% 0.21/0.50  fof(f450,plain,(
% 0.21/0.50    sK4(sK1) != sK4(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | v2_funct_1(sK1) | sK2 = sK3 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(superposition,[],[f37,f444])).
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    sK4(sK1) = sK5(sK1) | sK2 = sK3 | k1_xboole_0 = sK0),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f435])).
% 0.21/0.50  fof(f435,plain,(
% 0.21/0.50    sK2 = sK3 | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.50    inference(superposition,[],[f434,f423])).
% 0.21/0.50  fof(f423,plain,(
% 0.21/0.50    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.50    inference(subsumption_resolution,[],[f411,f371])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    v2_funct_1(sK1) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.50    inference(subsumption_resolution,[],[f370,f51])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    sK4(sK1) = sK5(sK1) | v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | ~r1_tarski(sK0,sK0)),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f367])).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    sK4(sK1) = sK5(sK1) | v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | ~r1_tarski(sK0,sK0) | v2_funct_1(sK1)),
% 0.21/0.50    inference(resolution,[],[f366,f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ( ! [X1] : (r2_hidden(sK4(sK1),X1) | ~r1_tarski(sK0,X1) | v2_funct_1(sK1)) )),
% 0.21/0.50    inference(resolution,[],[f133,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    v4_relat_1(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f47,f31])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v4_relat_1(sK1,X1) | r2_hidden(sK4(sK1),X0) | ~r1_tarski(X1,X0) | v2_funct_1(sK1)) )),
% 0.21/0.50    inference(resolution,[],[f129,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_relat_1(sK1),X0) | ~v4_relat_1(sK1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f39,f55])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK1),X0) | v2_funct_1(sK1) | r2_hidden(sK4(sK1),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f127,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X2,X3,X1] : (~r2_hidden(X1,X2) | r2_hidden(X1,X3) | ~r1_tarski(X2,X3)) )),
% 0.21/0.50    inference(resolution,[],[f40,f44])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK4(sK1),X0) | v2_funct_1(sK1) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f126,f55])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(sK1) | v2_funct_1(sK1) | r2_hidden(sK4(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 0.21/0.51    inference(resolution,[],[f92,f29])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0) | r2_hidden(sK4(X0),X1) | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 0.21/0.51    inference(resolution,[],[f34,f84])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  % (14410)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK1),sK0) | sK4(sK1) = sK5(sK1) | v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f365])).
% 0.21/0.51  fof(f365,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK1),sK0) | sK4(sK1) = sK5(sK1) | v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | sK4(sK1) = sK5(sK1)),
% 0.21/0.51    inference(equality_resolution,[],[f362])).
% 0.21/0.51  fof(f362,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | sK4(sK1) = sK5(sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f361,f51])).
% 0.21/0.51  fof(f361,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | sK4(sK1) = sK5(sK1) | ~r1_tarski(sK0,sK0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f358])).
% 0.21/0.51  fof(f358,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | sK4(sK1) = sK5(sK1) | ~r1_tarski(sK0,sK0) | v2_funct_1(sK1)) )),
% 0.21/0.51    inference(resolution,[],[f347,f151])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(sK5(sK1),X1) | ~r1_tarski(sK0,X1) | v2_funct_1(sK1)) )),
% 0.21/0.51    inference(resolution,[],[f148,f69])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v4_relat_1(sK1,X1) | r2_hidden(sK5(sK1),X0) | ~r1_tarski(X1,X0) | v2_funct_1(sK1)) )),
% 0.21/0.51    inference(resolution,[],[f146,f62])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK1),X0) | v2_funct_1(sK1) | r2_hidden(sK5(sK1),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f144,f84])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK5(sK1),X0) | v2_funct_1(sK1) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f143,f55])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(sK1) | v2_funct_1(sK1) | r2_hidden(sK5(sK1),X0) | ~r1_tarski(k1_relat_1(sK1),X0)) )),
% 0.21/0.51    inference(resolution,[],[f93,f29])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0) | r2_hidden(sK5(X0),X1) | ~r1_tarski(k1_relat_1(X0),X1)) )),
% 0.21/0.51    inference(resolution,[],[f35,f84])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK5(sK1),sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | v2_funct_1(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | sK4(sK1) = sK5(sK1)) )),
% 0.21/0.51    inference(superposition,[],[f28,f344])).
% 0.21/0.51  fof(f344,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | k1_xboole_0 = sK0 | sK2 = sK3 | sK4(sK1) = sK5(sK1)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f339])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    sK2 = sK3 | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.21/0.51    inference(superposition,[],[f312,f306])).
% 0.21/0.51  fof(f306,plain,(
% 0.21/0.51    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f305,f51])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~r1_tarski(sK0,sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f298])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~r1_tarski(sK0,sK0) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.21/0.51    inference(resolution,[],[f295,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(sK2,X1) | ~r1_tarski(sK0,X1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f100,f55])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X1] : (k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | ~r1_tarski(sK0,X1) | r2_hidden(sK2,X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f96,f29])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | ~r1_tarski(sK0,X1) | r2_hidden(sK2,X1)) )),
% 0.21/0.51    inference(resolution,[],[f36,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_funct_1(sK1) | ~r1_tarski(sK0,X0) | r2_hidden(sK2,X0)) )),
% 0.21/0.51    inference(resolution,[],[f84,f24])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f293,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(sK1,sK0,sK0) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))) )),
% 0.21/0.51    inference(resolution,[],[f292,f31])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK1,X0,X1) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X2)) = X2 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))) )),
% 0.21/0.51    inference(resolution,[],[f246,f29])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~r2_hidden(X3,X1) | k1_xboole_0 = X2 | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f245,f46])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X2 | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f238])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X0,X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | ~r2_hidden(X3,X1) | k1_xboole_0 = X2 | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f50,f36])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v2_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1)),
% 0.21/0.51    inference(superposition,[],[f307,f222])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | sK4(sK1) = sK5(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f221,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ~v2_funct_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | v2_funct_1(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f219,f51])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~r1_tarski(sK0,sK0) | v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f218,f136])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK1),sK0) | sK4(sK1) = sK5(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.51    inference(equality_resolution,[],[f216])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f215,f26])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | v2_funct_1(sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f213,f51])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~r1_tarski(sK0,sK0) | v2_funct_1(sK1)) )),
% 0.21/0.51    inference(resolution,[],[f158,f151])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK5(sK1),sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f156,f26])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(sK5(sK1),sK0) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | v2_funct_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)) )),
% 0.21/0.51    inference(superposition,[],[f28,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f55])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f97,f29])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.51    inference(resolution,[],[f36,f26])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f304,f51])).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~r1_tarski(sK0,sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f299])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~r1_tarski(sK0,sK0) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.21/0.51    inference(resolution,[],[f295,f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK3,X0) | ~r1_tarski(sK0,X0) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f55])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | ~r1_tarski(sK0,X0) | r2_hidden(sK3,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f29])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1) | ~r1_tarski(sK0,X0) | r2_hidden(sK3,X0)) )),
% 0.21/0.51    inference(resolution,[],[f36,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X1] : (~v2_funct_1(sK1) | ~r1_tarski(sK0,X1) | r2_hidden(sK3,X1)) )),
% 0.21/0.51    inference(resolution,[],[f84,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK0) | ~r2_hidden(X2,sK0) | X2 = X3 | v2_funct_1(sK1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f411,plain,(
% 0.21/0.51    sK2 = sK3 | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f410,f24])).
% 0.21/0.51  fof(f410,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | sK2 = sK3 | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f409,f30])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = sK0 | sK2 = sK3 | ~v1_funct_2(sK1,sK0,sK0) | sK4(sK1) = sK5(sK1) | ~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f407])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = sK0 | sK2 = sK3 | ~v1_funct_2(sK1,sK0,sK0) | sK4(sK1) = sK5(sK1) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.51    inference(resolution,[],[f380,f31])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK0 | sK2 = sK3 | ~v1_funct_2(sK1,X2,X3) | sK4(sK1) = sK5(sK1) | ~r2_hidden(X4,X2) | k1_xboole_0 = X3 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X4)) = X4) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f377,f29])).
% 0.21/0.51  fof(f377,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | ~v1_funct_2(sK1,X2,X3) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK1) | ~r2_hidden(X4,X2) | k1_xboole_0 = X3 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X4)) = X4) )),
% 0.21/0.51    inference(resolution,[],[f371,f50])).
% 0.21/0.51  fof(f434,plain,(
% 0.21/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f431])).
% 0.21/0.51  fof(f431,plain,(
% 0.21/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3 | sK4(sK1) = sK5(sK1)),
% 0.21/0.51    inference(superposition,[],[f424,f222])).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f412,f371])).
% 0.21/0.51  fof(f412,plain,(
% 0.21/0.51    sK2 = sK3 | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f410,f25])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (sK4(X0) != sK5(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f542,plain,(
% 0.21/0.51    sK2 = sK3 | k1_xboole_0 = sK0 | sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f541,f24])).
% 0.21/0.51  fof(f541,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | sK2 = sK3 | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f540,f30])).
% 0.21/0.51  fof(f540,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | sK2 = sK3 | ~r2_hidden(X0,sK0) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f538])).
% 0.21/0.51  fof(f538,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | sK2 = sK3 | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK0 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) )),
% 0.21/0.51    inference(resolution,[],[f463,f31])).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,X2,X3) | sK2 = sK3 | ~r2_hidden(X4,X2) | k1_xboole_0 = X3 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X4)) = X4) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f460,f29])).
% 0.21/0.51  fof(f460,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (sK2 = sK3 | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,X2,X3) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(sK1) | ~r2_hidden(X4,X2) | k1_xboole_0 = X3 | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X4)) = X4) )),
% 0.21/0.51    inference(resolution,[],[f454,f50])).
% 0.21/0.51  fof(f578,plain,(
% 0.21/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f574])).
% 0.21/0.51  fof(f574,plain,(
% 0.21/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | sK2 = sK3 | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.51    inference(superposition,[],[f559,f459])).
% 0.21/0.51  fof(f459,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.51    inference(resolution,[],[f454,f26])).
% 0.21/0.51  fof(f559,plain,(
% 0.21/0.51    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0 | sK2 = sK3),
% 0.21/0.51    inference(subsumption_resolution,[],[f543,f454])).
% 0.21/0.51  fof(f543,plain,(
% 0.21/0.51    sK2 = sK3 | k1_xboole_0 = sK0 | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f541,f25])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f666,plain,(
% 0.21/0.51    v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f665,f55])).
% 0.21/0.51  fof(f665,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f662,f29])).
% 0.21/0.51  fof(f662,plain,(
% 0.21/0.51    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f660])).
% 0.21/0.51  fof(f660,plain,(
% 0.21/0.51    sK4(sK1) != sK4(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | v2_funct_1(sK1) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(superposition,[],[f37,f651])).
% 0.21/0.51  fof(f651,plain,(
% 0.21/0.51    sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f650,f607])).
% 0.21/0.51  fof(f650,plain,(
% 0.21/0.51    sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | v2_funct_1(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f648,f51])).
% 0.21/0.51  fof(f648,plain,(
% 0.21/0.51    sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0 | ~r1_tarski(sK0,sK0) | v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f647,f136])).
% 0.21/0.51  fof(f647,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK1),sK0) | sK4(sK1) = sK5(sK1) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(equality_resolution,[],[f642])).
% 0.21/0.51  fof(f642,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | k1_xboole_0 = sK0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f641,f607])).
% 0.21/0.51  fof(f641,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | k1_xboole_0 = sK0 | v2_funct_1(sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f637,f51])).
% 0.21/0.51  fof(f637,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | k1_xboole_0 = sK0 | ~r1_tarski(sK0,sK0) | v2_funct_1(sK1)) )),
% 0.21/0.51    inference(resolution,[],[f627,f151])).
% 0.21/0.51  fof(f627,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK5(sK1),sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | k1_xboole_0 = sK0) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f623,f607])).
% 0.21/0.51  fof(f623,plain,(
% 0.21/0.51    ( ! [X0] : (k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | ~r2_hidden(sK5(sK1),sK0) | ~r2_hidden(X0,sK0) | sK5(sK1) = X0 | v2_funct_1(sK1) | k1_xboole_0 = sK0) )),
% 0.21/0.51    inference(superposition,[],[f28,f619])).
% 0.21/0.51  fof(f619,plain,(
% 0.21/0.51    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f618,f55])).
% 0.21/0.51  fof(f618,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f613,f29])).
% 0.21/0.51  fof(f613,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | ~v1_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f607,f36])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ~v4_relat_1(sK1,k1_xboole_0) | v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f128,f62])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ~r1_tarski(k1_relat_1(sK1),k1_xboole_0) | v2_funct_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f127,f81])).
% 0.21/0.51  fof(f675,plain,(
% 0.21/0.51    v4_relat_1(sK1,k1_xboole_0)),
% 0.21/0.51    inference(backward_demodulation,[],[f69,f667])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (14421)------------------------------
% 0.21/0.51  % (14421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14421)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (14421)Memory used [KB]: 2174
% 0.21/0.51  % (14421)Time elapsed: 0.091 s
% 0.21/0.51  % (14421)------------------------------
% 0.21/0.51  % (14421)------------------------------
% 0.21/0.51  % (14401)Success in time 0.15 s
%------------------------------------------------------------------------------
