%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:50 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 649 expanded)
%              Number of leaves         :   12 ( 133 expanded)
%              Depth                    :   22
%              Number of atoms          :  244 (2416 expanded)
%              Number of equality atoms :   76 ( 581 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f611,plain,(
    $false ),
    inference(subsumption_resolution,[],[f610,f510])).

fof(f510,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f135,f492])).

fof(f492,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f491,f135])).

fof(f491,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f489,f466])).

fof(f466,plain,(
    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) ),
    inference(subsumption_resolution,[],[f464,f135])).

fof(f464,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(factoring,[],[f387])).

fof(f387,plain,(
    ! [X13] :
      ( r2_hidden(sK4(X13,k2_relat_1(sK2)),sK1)
      | r2_hidden(sK4(X13,k2_relat_1(sK2)),X13)
      | k2_relat_1(sK2) = X13 ) ),
    inference(resolution,[],[f93,f308])).

fof(f308,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f304])).

fof(f304,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f303,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f303,plain,(
    ! [X1] :
      ( r2_hidden(sK5(k2_relat_1(sK2),X1),sK1)
      | r1_tarski(k2_relat_1(sK2),X1) ) ),
    inference(resolution,[],[f301,f82])).

fof(f82,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK2,X1)
      | r2_hidden(sK5(k2_relat_1(sK2),X0),X1)
      | r1_tarski(k2_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f92,f73])).

fof(f73,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(X6)
      | r1_tarski(k2_relat_1(X6),X7)
      | r2_hidden(sK5(k2_relat_1(X6),X7),X8)
      | ~ v5_relat_1(X6,X8) ) ),
    inference(resolution,[],[f80,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f80,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | r2_hidden(sK5(X2,X3),X4)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f40,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | X0 = X1
      | r2_hidden(sK4(X0,X1),X2)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(resolution,[],[f38,f40])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f489,plain,
    ( k1_xboole_0 = sK1
    | ~ r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f488,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(sK4(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f20])).

% (29335)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f488,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f487,f317])).

fof(f317,plain,(
    r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) ),
    inference(subsumption_resolution,[],[f316,f28])).

fof(f28,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f316,plain,
    ( r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) ),
    inference(subsumption_resolution,[],[f311,f135])).

fof(f311,plain,
    ( sK1 = k2_relat_1(sK2)
    | r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)
    | r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) ),
    inference(resolution,[],[f308,f172])).

fof(f172,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | sK1 = X1
      | r2_hidden(sK4(sK1,X1),X2)
      | r2_hidden(sK3(sK4(sK1,X1)),sK0) ) ),
    inference(resolution,[],[f170,f40])).

fof(f170,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),X0)
      | r2_hidden(sK3(sK4(sK1,X0)),sK0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f99,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f42,f41])).

fof(f99,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(sK0,X5)
      | sK1 = X4
      | r2_hidden(sK4(sK1,X4),X4)
      | r2_hidden(sK3(sK4(sK1,X4)),X5) ) ),
    inference(resolution,[],[f38,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r1_tarski(sK0,X1)
      | r2_hidden(sK3(X0),X1) ) ),
    inference(resolution,[],[f40,f28])).

fof(f487,plain,
    ( ~ r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)
    | r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f478,f330])).

fof(f330,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f329,f129])).

fof(f129,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f47,f32])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f329,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f328,f32])).

fof(f328,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f55,f31])).

fof(f31,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f478,plain,
    ( ~ r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),k1_relat_1(sK2))
    | r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(superposition,[],[f137,f468])).

fof(f468,plain,(
    sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2)))) ),
    inference(resolution,[],[f466,f29])).

fof(f29,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f137,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f136,f73])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f37,f30])).

% (29336)Refutation not found, incomplete strategy% (29336)------------------------------
% (29336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29336)Termination reason: Refutation not found, incomplete strategy

% (29336)Memory used [KB]: 10874
% (29336)Time elapsed: 0.166 s
% (29336)------------------------------
% (29336)------------------------------
fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

fof(f135,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f33,f132])).

fof(f132,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f48,f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f33,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f610,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f550,f67])).

fof(f67,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f34,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f550,plain,
    ( r2_hidden(sK4(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f313,f492])).

fof(f313,plain,
    ( r2_hidden(sK4(k1_xboole_0,k2_relat_1(sK2)),sK1)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f308,f112])).

fof(f112,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | r2_hidden(sK4(k1_xboole_0,X1),X2)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f98,f40])).

fof(f98,plain,(
    ! [X3] :
      ( r2_hidden(sK4(k1_xboole_0,X3),X3)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f38,f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : run_vampire %s %d
% 0.10/0.29  % Computer   : n014.cluster.edu
% 0.10/0.29  % Model      : x86_64 x86_64
% 0.10/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.29  % Memory     : 8042.1875MB
% 0.10/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.29  % CPULimit   : 60
% 0.10/0.29  % WCLimit    : 600
% 0.10/0.29  % DateTime   : Tue Dec  1 15:58:22 EST 2020
% 0.10/0.29  % CPUTime    : 
% 0.15/0.46  % (29337)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.15/0.47  % (29337)Refutation not found, incomplete strategy% (29337)------------------------------
% 0.15/0.47  % (29337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.47  % (29320)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.15/0.47  % (29328)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.15/0.47  % (29337)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.47  
% 0.15/0.47  % (29337)Memory used [KB]: 1791
% 0.15/0.47  % (29337)Time elapsed: 0.101 s
% 0.15/0.47  % (29337)------------------------------
% 0.15/0.47  % (29337)------------------------------
% 0.15/0.48  % (29329)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.15/0.49  % (29344)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.15/0.50  % (29319)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.15/0.50  % (29327)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.15/0.51  % (29341)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.15/0.51  % (29336)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.15/0.51  % (29320)Refutation found. Thanks to Tanya!
% 0.15/0.51  % SZS status Theorem for theBenchmark
% 0.15/0.51  % (29315)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.15/0.51  % SZS output start Proof for theBenchmark
% 0.15/0.51  fof(f611,plain,(
% 0.15/0.51    $false),
% 0.15/0.51    inference(subsumption_resolution,[],[f610,f510])).
% 0.15/0.51  fof(f510,plain,(
% 0.15/0.51    k1_xboole_0 != k2_relat_1(sK2)),
% 0.15/0.51    inference(backward_demodulation,[],[f135,f492])).
% 0.15/0.51  fof(f492,plain,(
% 0.15/0.51    k1_xboole_0 = sK1),
% 0.15/0.51    inference(subsumption_resolution,[],[f491,f135])).
% 0.15/0.51  fof(f491,plain,(
% 0.15/0.51    k1_xboole_0 = sK1 | sK1 = k2_relat_1(sK2)),
% 0.15/0.51    inference(subsumption_resolution,[],[f489,f466])).
% 0.15/0.51  fof(f466,plain,(
% 0.15/0.51    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1)),
% 0.15/0.51    inference(subsumption_resolution,[],[f464,f135])).
% 0.15/0.51  fof(f464,plain,(
% 0.15/0.51    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | sK1 = k2_relat_1(sK2)),
% 0.15/0.51    inference(factoring,[],[f387])).
% 0.15/0.51  fof(f387,plain,(
% 0.15/0.51    ( ! [X13] : (r2_hidden(sK4(X13,k2_relat_1(sK2)),sK1) | r2_hidden(sK4(X13,k2_relat_1(sK2)),X13) | k2_relat_1(sK2) = X13) )),
% 0.15/0.51    inference(resolution,[],[f93,f308])).
% 0.15/0.51  fof(f308,plain,(
% 0.15/0.51    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.15/0.51    inference(duplicate_literal_removal,[],[f304])).
% 0.15/0.51  fof(f304,plain,(
% 0.15/0.51    r1_tarski(k2_relat_1(sK2),sK1) | r1_tarski(k2_relat_1(sK2),sK1)),
% 0.15/0.51    inference(resolution,[],[f303,f42])).
% 0.15/0.51  fof(f42,plain,(
% 0.15/0.51    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.15/0.51    inference(cnf_transformation,[],[f21])).
% 0.15/0.51  fof(f21,plain,(
% 0.15/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.15/0.51    inference(ennf_transformation,[],[f1])).
% 0.15/0.51  fof(f1,axiom,(
% 0.15/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.15/0.51  fof(f303,plain,(
% 0.15/0.51    ( ! [X1] : (r2_hidden(sK5(k2_relat_1(sK2),X1),sK1) | r1_tarski(k2_relat_1(sK2),X1)) )),
% 0.15/0.51    inference(resolution,[],[f301,f82])).
% 0.15/0.51  fof(f82,plain,(
% 0.15/0.51    v5_relat_1(sK2,sK1)),
% 0.15/0.51    inference(resolution,[],[f49,f32])).
% 0.15/0.51  fof(f32,plain,(
% 0.15/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.15/0.51    inference(cnf_transformation,[],[f16])).
% 0.15/0.51  fof(f16,plain,(
% 0.15/0.51    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.15/0.51    inference(flattening,[],[f15])).
% 0.15/0.51  fof(f15,plain,(
% 0.15/0.51    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.15/0.51    inference(ennf_transformation,[],[f13])).
% 0.15/0.51  fof(f13,negated_conjecture,(
% 0.15/0.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.15/0.51    inference(negated_conjecture,[],[f12])).
% 0.15/0.51  fof(f12,conjecture,(
% 0.15/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.15/0.51  fof(f49,plain,(
% 0.15/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.15/0.51    inference(cnf_transformation,[],[f25])).
% 0.15/0.51  fof(f25,plain,(
% 0.15/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.15/0.51    inference(ennf_transformation,[],[f14])).
% 0.15/0.51  fof(f14,plain,(
% 0.15/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.15/0.51    inference(pure_predicate_removal,[],[f8])).
% 0.15/0.51  fof(f8,axiom,(
% 0.15/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.15/0.51  fof(f301,plain,(
% 0.15/0.51    ( ! [X0,X1] : (~v5_relat_1(sK2,X1) | r2_hidden(sK5(k2_relat_1(sK2),X0),X1) | r1_tarski(k2_relat_1(sK2),X0)) )),
% 0.15/0.51    inference(resolution,[],[f92,f73])).
% 0.15/0.51  fof(f73,plain,(
% 0.15/0.51    v1_relat_1(sK2)),
% 0.15/0.51    inference(resolution,[],[f46,f32])).
% 0.15/0.51  fof(f46,plain,(
% 0.15/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.15/0.51    inference(cnf_transformation,[],[f22])).
% 0.15/0.51  fof(f22,plain,(
% 0.15/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.15/0.51    inference(ennf_transformation,[],[f7])).
% 0.15/0.51  fof(f7,axiom,(
% 0.15/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.15/0.51  fof(f92,plain,(
% 0.15/0.51    ( ! [X6,X8,X7] : (~v1_relat_1(X6) | r1_tarski(k2_relat_1(X6),X7) | r2_hidden(sK5(k2_relat_1(X6),X7),X8) | ~v5_relat_1(X6,X8)) )),
% 0.15/0.51    inference(resolution,[],[f80,f36])).
% 0.15/0.51  fof(f36,plain,(
% 0.15/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.15/0.51    inference(cnf_transformation,[],[f17])).
% 0.15/0.51  fof(f17,plain,(
% 0.15/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.15/0.51    inference(ennf_transformation,[],[f5])).
% 0.15/0.51  fof(f5,axiom,(
% 0.15/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.15/0.51  fof(f80,plain,(
% 0.15/0.51    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | r2_hidden(sK5(X2,X3),X4) | r1_tarski(X2,X3)) )),
% 0.15/0.51    inference(resolution,[],[f40,f41])).
% 0.15/0.51  fof(f41,plain,(
% 0.15/0.51    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.15/0.51    inference(cnf_transformation,[],[f21])).
% 0.15/0.51  fof(f40,plain,(
% 0.15/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.15/0.51    inference(cnf_transformation,[],[f21])).
% 0.15/0.51  fof(f93,plain,(
% 0.15/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | X0 = X1 | r2_hidden(sK4(X0,X1),X2) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.15/0.51    inference(resolution,[],[f38,f40])).
% 0.15/0.51  fof(f38,plain,(
% 0.15/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.15/0.51    inference(cnf_transformation,[],[f20])).
% 0.15/0.51  fof(f20,plain,(
% 0.15/0.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.15/0.51    inference(ennf_transformation,[],[f2])).
% 0.15/0.51  fof(f2,axiom,(
% 0.15/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.15/0.51  fof(f489,plain,(
% 0.15/0.51    k1_xboole_0 = sK1 | ~r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | sK1 = k2_relat_1(sK2)),
% 0.15/0.51    inference(resolution,[],[f488,f39])).
% 0.15/0.51  fof(f39,plain,(
% 0.15/0.51    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(sK4(X0,X1),X0) | X0 = X1) )),
% 0.15/0.51    inference(cnf_transformation,[],[f20])).
% 0.15/0.51  % (29335)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.15/0.51  fof(f488,plain,(
% 0.15/0.51    r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | k1_xboole_0 = sK1),
% 0.15/0.51    inference(subsumption_resolution,[],[f487,f317])).
% 0.15/0.51  fof(f317,plain,(
% 0.15/0.51    r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)),
% 0.15/0.51    inference(subsumption_resolution,[],[f316,f28])).
% 0.15/0.51  fof(f28,plain,(
% 0.15/0.51    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.15/0.51    inference(cnf_transformation,[],[f16])).
% 0.15/0.51  fof(f316,plain,(
% 0.15/0.51    r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)),
% 0.15/0.51    inference(subsumption_resolution,[],[f311,f135])).
% 0.15/0.51  fof(f311,plain,(
% 0.15/0.51    sK1 = k2_relat_1(sK2) | r2_hidden(sK4(sK1,k2_relat_1(sK2)),sK1) | r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0)),
% 0.15/0.51    inference(resolution,[],[f308,f172])).
% 0.15/0.51  fof(f172,plain,(
% 0.15/0.51    ( ! [X2,X1] : (~r1_tarski(X1,X2) | sK1 = X1 | r2_hidden(sK4(sK1,X1),X2) | r2_hidden(sK3(sK4(sK1,X1)),sK0)) )),
% 0.15/0.51    inference(resolution,[],[f170,f40])).
% 0.15/0.51  fof(f170,plain,(
% 0.15/0.51    ( ! [X0] : (r2_hidden(sK4(sK1,X0),X0) | r2_hidden(sK3(sK4(sK1,X0)),sK0) | sK1 = X0) )),
% 0.15/0.51    inference(resolution,[],[f99,f72])).
% 0.15/0.51  fof(f72,plain,(
% 0.15/0.51    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.15/0.51    inference(duplicate_literal_removal,[],[f71])).
% 0.15/0.51  fof(f71,plain,(
% 0.15/0.51    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.15/0.51    inference(resolution,[],[f42,f41])).
% 0.15/0.51  fof(f99,plain,(
% 0.15/0.51    ( ! [X4,X5] : (~r1_tarski(sK0,X5) | sK1 = X4 | r2_hidden(sK4(sK1,X4),X4) | r2_hidden(sK3(sK4(sK1,X4)),X5)) )),
% 0.15/0.51    inference(resolution,[],[f38,f79])).
% 0.15/0.51  fof(f79,plain,(
% 0.15/0.51    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~r1_tarski(sK0,X1) | r2_hidden(sK3(X0),X1)) )),
% 0.15/0.51    inference(resolution,[],[f40,f28])).
% 0.15/0.51  fof(f487,plain,(
% 0.15/0.51    ~r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),sK0) | r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2)) | k1_xboole_0 = sK1),
% 0.15/0.51    inference(superposition,[],[f478,f330])).
% 0.15/0.51  fof(f330,plain,(
% 0.15/0.51    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1),
% 0.15/0.51    inference(superposition,[],[f329,f129])).
% 0.15/0.51  fof(f129,plain,(
% 0.15/0.51    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.15/0.51    inference(resolution,[],[f47,f32])).
% 0.15/0.51  fof(f47,plain,(
% 0.15/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.15/0.51    inference(cnf_transformation,[],[f23])).
% 0.15/0.51  fof(f23,plain,(
% 0.15/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.15/0.51    inference(ennf_transformation,[],[f9])).
% 0.15/0.51  fof(f9,axiom,(
% 0.15/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.15/0.51  fof(f329,plain,(
% 0.15/0.51    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.15/0.51    inference(subsumption_resolution,[],[f328,f32])).
% 0.15/0.51  fof(f328,plain,(
% 0.15/0.51    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.15/0.51    inference(resolution,[],[f55,f31])).
% 0.15/0.51  fof(f31,plain,(
% 0.15/0.51    v1_funct_2(sK2,sK0,sK1)),
% 0.15/0.51    inference(cnf_transformation,[],[f16])).
% 0.15/0.51  fof(f55,plain,(
% 0.15/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.15/0.51    inference(cnf_transformation,[],[f27])).
% 0.15/0.51  fof(f27,plain,(
% 0.15/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.15/0.51    inference(flattening,[],[f26])).
% 0.15/0.51  fof(f26,plain,(
% 0.15/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.15/0.51    inference(ennf_transformation,[],[f11])).
% 0.15/0.51  fof(f11,axiom,(
% 0.15/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.15/0.51  fof(f478,plain,(
% 0.15/0.51    ~r2_hidden(sK3(sK4(sK1,k2_relat_1(sK2))),k1_relat_1(sK2)) | r2_hidden(sK4(sK1,k2_relat_1(sK2)),k2_relat_1(sK2))),
% 0.15/0.51    inference(superposition,[],[f137,f468])).
% 0.15/0.51  fof(f468,plain,(
% 0.15/0.51    sK4(sK1,k2_relat_1(sK2)) = k1_funct_1(sK2,sK3(sK4(sK1,k2_relat_1(sK2))))),
% 0.15/0.51    inference(resolution,[],[f466,f29])).
% 0.15/0.51  fof(f29,plain,(
% 0.15/0.51    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.15/0.51    inference(cnf_transformation,[],[f16])).
% 0.15/0.51  fof(f137,plain,(
% 0.15/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,k1_relat_1(sK2))) )),
% 0.15/0.51    inference(subsumption_resolution,[],[f136,f73])).
% 0.15/0.51  fof(f136,plain,(
% 0.15/0.51    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))) )),
% 0.15/0.51    inference(resolution,[],[f37,f30])).
% 0.15/0.51  % (29336)Refutation not found, incomplete strategy% (29336)------------------------------
% 0.15/0.51  % (29336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.51  % (29336)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.51  
% 0.15/0.51  % (29336)Memory used [KB]: 10874
% 0.15/0.51  % (29336)Time elapsed: 0.166 s
% 0.15/0.51  % (29336)------------------------------
% 0.15/0.51  % (29336)------------------------------
% 0.15/0.51  fof(f30,plain,(
% 0.15/0.51    v1_funct_1(sK2)),
% 0.15/0.51    inference(cnf_transformation,[],[f16])).
% 0.15/0.51  fof(f37,plain,(
% 0.15/0.51    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))) )),
% 0.15/0.51    inference(cnf_transformation,[],[f19])).
% 0.15/0.51  fof(f19,plain,(
% 0.15/0.51    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.15/0.51    inference(flattening,[],[f18])).
% 0.15/0.51  fof(f18,plain,(
% 0.15/0.51    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.15/0.51    inference(ennf_transformation,[],[f6])).
% 0.15/0.51  fof(f6,axiom,(
% 0.15/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).
% 0.15/0.51  fof(f135,plain,(
% 0.15/0.51    sK1 != k2_relat_1(sK2)),
% 0.15/0.51    inference(superposition,[],[f33,f132])).
% 0.15/0.51  fof(f132,plain,(
% 0.15/0.51    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.15/0.51    inference(resolution,[],[f48,f32])).
% 0.15/0.51  fof(f48,plain,(
% 0.15/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.15/0.51    inference(cnf_transformation,[],[f24])).
% 0.15/0.51  fof(f24,plain,(
% 0.15/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.15/0.51    inference(ennf_transformation,[],[f10])).
% 0.15/0.51  fof(f10,axiom,(
% 0.15/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.15/0.51  fof(f33,plain,(
% 0.15/0.51    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.15/0.51    inference(cnf_transformation,[],[f16])).
% 0.15/0.51  fof(f610,plain,(
% 0.15/0.51    k1_xboole_0 = k2_relat_1(sK2)),
% 0.15/0.51    inference(subsumption_resolution,[],[f550,f67])).
% 0.15/0.51  fof(f67,plain,(
% 0.15/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.15/0.51    inference(superposition,[],[f34,f56])).
% 0.15/0.51  fof(f56,plain,(
% 0.15/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.15/0.51    inference(equality_resolution,[],[f45])).
% 0.15/0.51  fof(f45,plain,(
% 0.15/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.15/0.51    inference(cnf_transformation,[],[f3])).
% 0.15/0.51  fof(f3,axiom,(
% 0.15/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.15/0.51  fof(f34,plain,(
% 0.15/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.15/0.51    inference(cnf_transformation,[],[f4])).
% 0.15/0.51  fof(f4,axiom,(
% 0.15/0.51    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.15/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.15/0.52  fof(f550,plain,(
% 0.15/0.52    r2_hidden(sK4(k1_xboole_0,k2_relat_1(sK2)),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.15/0.52    inference(backward_demodulation,[],[f313,f492])).
% 0.15/0.52  fof(f313,plain,(
% 0.15/0.52    r2_hidden(sK4(k1_xboole_0,k2_relat_1(sK2)),sK1) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.15/0.52    inference(resolution,[],[f308,f112])).
% 0.15/0.52  fof(f112,plain,(
% 0.15/0.52    ( ! [X2,X1] : (~r1_tarski(X1,X2) | r2_hidden(sK4(k1_xboole_0,X1),X2) | k1_xboole_0 = X1) )),
% 0.15/0.52    inference(resolution,[],[f98,f40])).
% 0.15/0.52  fof(f98,plain,(
% 0.15/0.52    ( ! [X3] : (r2_hidden(sK4(k1_xboole_0,X3),X3) | k1_xboole_0 = X3) )),
% 0.15/0.52    inference(resolution,[],[f38,f67])).
% 0.15/0.52  % SZS output end Proof for theBenchmark
% 0.15/0.52  % (29320)------------------------------
% 0.15/0.52  % (29320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.52  % (29320)Termination reason: Refutation
% 0.15/0.52  
% 0.15/0.52  % (29320)Memory used [KB]: 6652
% 0.15/0.52  % (29320)Time elapsed: 0.128 s
% 0.15/0.52  % (29320)------------------------------
% 0.15/0.52  % (29320)------------------------------
% 0.15/0.52  % (29307)Success in time 0.21 s
%------------------------------------------------------------------------------
