%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 395 expanded)
%              Number of leaves         :   14 ( 126 expanded)
%              Depth                    :   17
%              Number of atoms          :  323 (2604 expanded)
%              Number of equality atoms :   73 ( 705 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f272,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f145,f242,f271])).

fof(f271,plain,(
    ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f267,f197])).

fof(f197,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f30,f194])).

fof(f194,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f193,f27])).

fof(f27,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK2 != sK3
    & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    & r2_hidden(sK3,sK0)
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        & v2_funct_1(X1)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X3,X2] :
          ( X2 != X3
          & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
          & r2_hidden(X3,sK0)
          & r2_hidden(X2,sK0) )
      & v2_funct_1(sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X3,X2] :
        ( X2 != X3
        & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3)
        & r2_hidden(X3,sK0)
        & r2_hidden(X2,sK0) )
   => ( sK2 != sK3
      & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
      & r2_hidden(sK3,sK0)
      & r2_hidden(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).

fof(f193,plain,
    ( k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f191,f30])).

fof(f191,plain,
    ( ~ r2_hidden(sK2,sK0)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f154,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ r2_hidden(sK2,X1)
        | k1_xboole_0 = X0
        | ~ v1_funct_2(sK1,X1,X0) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f153,f26])).

fof(f26,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(sK2,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK1,X1,X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f152,f29])).

fof(f29,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r2_hidden(sK2,X1)
        | ~ v2_funct_1(sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK1,X1,X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f146,f33])).

fof(f33,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( sK2 = sK3
        | k1_xboole_0 = X0
        | ~ r2_hidden(sK2,X1)
        | ~ v2_funct_1(sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK1,X1,X0)
        | ~ v1_funct_1(sK1) )
    | ~ spl4_6 ),
    inference(superposition,[],[f102,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).

fof(f102,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_6
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f30,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f267,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f158,f258])).

fof(f258,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f202,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f39,f34])).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f202,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f76,f194])).

fof(f76,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f73,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f72,f28])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f44,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f158,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f157,f50])).

fof(f50,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f42,f28])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f157,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f156,f26])).

fof(f156,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f155,f29])).

fof(f155,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f147,f33])).

fof(f147,plain,
    ( sK2 = sK3
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl4_6 ),
    inference(superposition,[],[f102,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).

fof(f242,plain,
    ( spl4_5
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f239,f225])).

fof(f225,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f31,f221])).

fof(f221,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f220,f31])).

fof(f220,plain,
    ( ~ r2_hidden(sK3,sK0)
    | k1_xboole_0 = sK0
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f218,f27])).

fof(f218,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ r2_hidden(sK3,sK0)
    | k1_xboole_0 = sK0
    | ~ spl4_7 ),
    inference(resolution,[],[f144,f28])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK1,X1,X0)
        | ~ r2_hidden(sK3,X1)
        | k1_xboole_0 = X0 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK1,X1,X0)
        | ~ r2_hidden(sK3,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f31,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f239,plain,
    ( ~ r2_hidden(sK3,k1_xboole_0)
    | spl4_5
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f98,f235])).

fof(f235,plain,
    ( k1_xboole_0 = k1_relat_1(sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f229,f52])).

fof(f229,plain,
    ( r1_tarski(k1_relat_1(sK1),k1_xboole_0)
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f76,f221])).

fof(f98,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK1))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_5
  <=> r2_hidden(sK3,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f145,plain,
    ( spl4_7
    | spl4_6 ),
    inference(avatar_split_clause,[],[f141,f100,f143])).

fof(f141,plain,(
    ! [X0,X1] :
      ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
      | k1_xboole_0 = X0
      | ~ r2_hidden(sK3,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK1,X1,X0) ) ),
    inference(subsumption_resolution,[],[f140,f26])).

fof(f140,plain,(
    ! [X0,X1] :
      ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
      | k1_xboole_0 = X0
      | ~ r2_hidden(sK3,X1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK1,X1,X0)
      | ~ v1_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f134,f29])).

fof(f134,plain,(
    ! [X0,X1] :
      ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
      | k1_xboole_0 = X0
      | ~ r2_hidden(sK3,X1)
      | ~ v2_funct_1(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK1,X1,X0)
      | ~ v1_funct_1(sK1) ) ),
    inference(superposition,[],[f45,f32])).

fof(f32,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f103,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f94,f100,f96])).

fof(f94,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f93,f50])).

fof(f93,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f92,f26])).

fof(f92,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f90,f29])).

fof(f90,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f35,f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:01:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (21559)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (21540)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (21543)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (21556)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (21540)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (21539)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (21548)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (21557)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (21549)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (21553)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.52  % (21536)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (21549)Refutation not found, incomplete strategy% (21549)------------------------------
% 0.22/0.52  % (21549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21552)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (21549)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21549)Memory used [KB]: 6268
% 0.22/0.53  % (21549)Time elapsed: 0.069 s
% 0.22/0.53  % (21549)------------------------------
% 0.22/0.53  % (21549)------------------------------
% 0.22/0.53  % (21551)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (21545)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (21560)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (21536)Refutation not found, incomplete strategy% (21536)------------------------------
% 0.22/0.53  % (21536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21536)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21536)Memory used [KB]: 10618
% 0.22/0.53  % (21536)Time elapsed: 0.076 s
% 0.22/0.53  % (21536)------------------------------
% 0.22/0.53  % (21536)------------------------------
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f103,f145,f242,f271])).
% 0.22/0.53  fof(f271,plain,(
% 0.22/0.53    ~spl4_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f270])).
% 0.22/0.53  fof(f270,plain,(
% 0.22/0.53    $false | ~spl4_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f267,f197])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    r2_hidden(sK2,k1_xboole_0) | ~spl4_6),
% 0.22/0.53    inference(backward_demodulation,[],[f30,f194])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | ~spl4_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f193,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f21,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) & v2_funct_1(sK1) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ? [X3,X2] : (X2 != X3 & k1_funct_1(sK1,X2) = k1_funct_1(sK1,X3) & r2_hidden(X3,sK0) & r2_hidden(X2,sK0)) => (sK2 != sK3 & k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) & r2_hidden(sK3,sK0) & r2_hidden(sK2,sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~spl4_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f191,f30])).
% 0.22/0.53  fof(f191,plain,(
% 0.22/0.53    ~r2_hidden(sK2,sK0) | k1_xboole_0 = sK0 | ~v1_funct_2(sK1,sK0,sK0) | ~spl4_6),
% 0.22/0.53    inference(resolution,[],[f154,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_hidden(sK2,X1) | k1_xboole_0 = X0 | ~v1_funct_2(sK1,X1,X0)) ) | ~spl4_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f153,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    v1_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK2,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK1,X1,X0) | ~v1_funct_1(sK1)) ) | ~spl4_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f152,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    v2_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r2_hidden(sK2,X1) | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK1,X1,X0) | ~v1_funct_1(sK1)) ) | ~spl4_6),
% 0.22/0.53    inference(subsumption_resolution,[],[f146,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    sK2 != sK3),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 1.19/0.53  fof(f146,plain,(
% 1.19/0.53    ( ! [X0,X1] : (sK2 = sK3 | k1_xboole_0 = X0 | ~r2_hidden(sK2,X1) | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK1,X1,X0) | ~v1_funct_1(sK1)) ) | ~spl4_6),
% 1.19/0.53    inference(superposition,[],[f102,f45])).
% 1.19/0.53  fof(f45,plain,(
% 1.19/0.53    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f19])).
% 1.19/0.53  fof(f19,plain,(
% 1.19/0.53    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.19/0.53    inference(flattening,[],[f18])).
% 1.19/0.53  fof(f18,plain,(
% 1.19/0.53    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.19/0.53    inference(ennf_transformation,[],[f8])).
% 1.19/0.53  fof(f8,axiom,(
% 1.19/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_funct_2)).
% 1.19/0.53  fof(f102,plain,(
% 1.19/0.53    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_6),
% 1.19/0.53    inference(avatar_component_clause,[],[f100])).
% 1.19/0.53  fof(f100,plain,(
% 1.19/0.53    spl4_6 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.19/0.53  fof(f30,plain,(
% 1.19/0.53    r2_hidden(sK2,sK0)),
% 1.19/0.53    inference(cnf_transformation,[],[f22])).
% 1.19/0.53  fof(f267,plain,(
% 1.19/0.53    ~r2_hidden(sK2,k1_xboole_0) | ~spl4_6),
% 1.19/0.53    inference(backward_demodulation,[],[f158,f258])).
% 1.19/0.53  fof(f258,plain,(
% 1.19/0.53    k1_xboole_0 = k1_relat_1(sK1) | ~spl4_6),
% 1.19/0.53    inference(resolution,[],[f202,f52])).
% 1.19/0.53  fof(f52,plain,(
% 1.19/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.19/0.53    inference(resolution,[],[f39,f34])).
% 1.19/0.53  fof(f34,plain,(
% 1.19/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f2])).
% 1.19/0.53  fof(f2,axiom,(
% 1.19/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.19/0.53  fof(f39,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f24])).
% 1.19/0.53  fof(f24,plain,(
% 1.19/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.19/0.53    inference(flattening,[],[f23])).
% 1.19/0.53  fof(f23,plain,(
% 1.19/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.19/0.53    inference(nnf_transformation,[],[f1])).
% 1.19/0.53  fof(f1,axiom,(
% 1.19/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.19/0.53  fof(f202,plain,(
% 1.19/0.53    r1_tarski(k1_relat_1(sK1),k1_xboole_0) | ~spl4_6),
% 1.19/0.53    inference(backward_demodulation,[],[f76,f194])).
% 1.19/0.53  fof(f76,plain,(
% 1.19/0.53    r1_tarski(k1_relat_1(sK1),sK0)),
% 1.19/0.53    inference(resolution,[],[f73,f40])).
% 1.19/0.53  fof(f40,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f25])).
% 1.19/0.53  fof(f25,plain,(
% 1.19/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.19/0.53    inference(nnf_transformation,[],[f3])).
% 1.19/0.53  fof(f3,axiom,(
% 1.19/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.19/0.53  fof(f73,plain,(
% 1.19/0.53    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 1.19/0.53    inference(resolution,[],[f72,f28])).
% 1.19/0.53  fof(f72,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))) )),
% 1.19/0.53    inference(duplicate_literal_removal,[],[f71])).
% 1.19/0.53  fof(f71,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.53    inference(superposition,[],[f44,f43])).
% 1.19/0.53  fof(f43,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f16])).
% 1.19/0.53  fof(f16,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f7])).
% 1.19/0.53  fof(f7,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.19/0.53  fof(f44,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.53    inference(cnf_transformation,[],[f17])).
% 1.19/0.53  fof(f17,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f6])).
% 1.19/0.53  fof(f6,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.19/0.53  fof(f158,plain,(
% 1.19/0.53    ~r2_hidden(sK2,k1_relat_1(sK1)) | ~spl4_6),
% 1.19/0.53    inference(subsumption_resolution,[],[f157,f50])).
% 1.19/0.53  fof(f50,plain,(
% 1.19/0.53    v1_relat_1(sK1)),
% 1.19/0.53    inference(resolution,[],[f42,f28])).
% 1.19/0.53  fof(f42,plain,(
% 1.19/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f15])).
% 1.19/0.53  fof(f15,plain,(
% 1.19/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.53    inference(ennf_transformation,[],[f5])).
% 1.19/0.53  fof(f5,axiom,(
% 1.19/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.19/0.53  fof(f157,plain,(
% 1.19/0.53    ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl4_6),
% 1.19/0.53    inference(subsumption_resolution,[],[f156,f26])).
% 1.19/0.53  fof(f156,plain,(
% 1.19/0.53    ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_6),
% 1.19/0.53    inference(subsumption_resolution,[],[f155,f29])).
% 1.19/0.53  fof(f155,plain,(
% 1.19/0.53    ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_6),
% 1.19/0.53    inference(subsumption_resolution,[],[f147,f33])).
% 1.19/0.53  fof(f147,plain,(
% 1.19/0.53    sK2 = sK3 | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl4_6),
% 1.19/0.53    inference(superposition,[],[f102,f35])).
% 1.19/0.53  fof(f35,plain,(
% 1.19/0.53    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.19/0.53    inference(cnf_transformation,[],[f14])).
% 1.19/0.53  fof(f14,plain,(
% 1.19/0.53    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.19/0.53    inference(flattening,[],[f13])).
% 1.19/0.53  fof(f13,plain,(
% 1.19/0.53    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.19/0.53    inference(ennf_transformation,[],[f4])).
% 1.19/0.53  fof(f4,axiom,(
% 1.19/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 1.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_funct_1)).
% 1.19/0.53  fof(f242,plain,(
% 1.19/0.53    spl4_5 | ~spl4_7),
% 1.19/0.53    inference(avatar_contradiction_clause,[],[f241])).
% 1.19/0.53  fof(f241,plain,(
% 1.19/0.53    $false | (spl4_5 | ~spl4_7)),
% 1.19/0.53    inference(subsumption_resolution,[],[f239,f225])).
% 1.19/0.53  fof(f225,plain,(
% 1.19/0.53    r2_hidden(sK3,k1_xboole_0) | ~spl4_7),
% 1.19/0.53    inference(backward_demodulation,[],[f31,f221])).
% 1.19/0.53  fof(f221,plain,(
% 1.19/0.53    k1_xboole_0 = sK0 | ~spl4_7),
% 1.19/0.53    inference(subsumption_resolution,[],[f220,f31])).
% 1.19/0.53  fof(f220,plain,(
% 1.19/0.53    ~r2_hidden(sK3,sK0) | k1_xboole_0 = sK0 | ~spl4_7),
% 1.19/0.53    inference(subsumption_resolution,[],[f218,f27])).
% 1.19/0.53  fof(f218,plain,(
% 1.19/0.53    ~v1_funct_2(sK1,sK0,sK0) | ~r2_hidden(sK3,sK0) | k1_xboole_0 = sK0 | ~spl4_7),
% 1.19/0.53    inference(resolution,[],[f144,f28])).
% 1.19/0.53  fof(f144,plain,(
% 1.19/0.53    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK1,X1,X0) | ~r2_hidden(sK3,X1) | k1_xboole_0 = X0) ) | ~spl4_7),
% 1.19/0.53    inference(avatar_component_clause,[],[f143])).
% 1.19/0.53  fof(f143,plain,(
% 1.19/0.53    spl4_7 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v1_funct_2(sK1,X1,X0) | ~r2_hidden(sK3,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.19/0.53  fof(f31,plain,(
% 1.19/0.53    r2_hidden(sK3,sK0)),
% 1.19/0.53    inference(cnf_transformation,[],[f22])).
% 1.19/0.53  fof(f239,plain,(
% 1.19/0.53    ~r2_hidden(sK3,k1_xboole_0) | (spl4_5 | ~spl4_7)),
% 1.19/0.53    inference(backward_demodulation,[],[f98,f235])).
% 1.19/0.53  fof(f235,plain,(
% 1.19/0.53    k1_xboole_0 = k1_relat_1(sK1) | ~spl4_7),
% 1.19/0.53    inference(resolution,[],[f229,f52])).
% 1.19/0.53  fof(f229,plain,(
% 1.19/0.53    r1_tarski(k1_relat_1(sK1),k1_xboole_0) | ~spl4_7),
% 1.19/0.53    inference(backward_demodulation,[],[f76,f221])).
% 1.19/0.53  fof(f98,plain,(
% 1.19/0.53    ~r2_hidden(sK3,k1_relat_1(sK1)) | spl4_5),
% 1.19/0.53    inference(avatar_component_clause,[],[f96])).
% 1.19/0.53  fof(f96,plain,(
% 1.19/0.53    spl4_5 <=> r2_hidden(sK3,k1_relat_1(sK1))),
% 1.19/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.19/0.53  fof(f145,plain,(
% 1.19/0.53    spl4_7 | spl4_6),
% 1.19/0.53    inference(avatar_split_clause,[],[f141,f100,f143])).
% 1.19/0.53  fof(f141,plain,(
% 1.19/0.53    ( ! [X0,X1] : (sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = X0 | ~r2_hidden(sK3,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK1,X1,X0)) )),
% 1.19/0.53    inference(subsumption_resolution,[],[f140,f26])).
% 1.19/0.53  fof(f140,plain,(
% 1.19/0.53    ( ! [X0,X1] : (sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = X0 | ~r2_hidden(sK3,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK1,X1,X0) | ~v1_funct_1(sK1)) )),
% 1.19/0.53    inference(subsumption_resolution,[],[f134,f29])).
% 1.19/0.53  fof(f134,plain,(
% 1.19/0.53    ( ! [X0,X1] : (sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = X0 | ~r2_hidden(sK3,X1) | ~v2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK1,X1,X0) | ~v1_funct_1(sK1)) )),
% 1.19/0.53    inference(superposition,[],[f45,f32])).
% 1.19/0.53  fof(f32,plain,(
% 1.19/0.53    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 1.19/0.53    inference(cnf_transformation,[],[f22])).
% 1.19/0.53  fof(f103,plain,(
% 1.19/0.53    ~spl4_5 | spl4_6),
% 1.19/0.53    inference(avatar_split_clause,[],[f94,f100,f96])).
% 1.19/0.53  fof(f94,plain,(
% 1.19/0.53    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,k1_relat_1(sK1))),
% 1.19/0.53    inference(subsumption_resolution,[],[f93,f50])).
% 1.19/0.53  fof(f93,plain,(
% 1.19/0.53    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 1.19/0.53    inference(subsumption_resolution,[],[f92,f26])).
% 1.19/0.53  fof(f92,plain,(
% 1.19/0.53    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.19/0.53    inference(subsumption_resolution,[],[f90,f29])).
% 1.19/0.53  fof(f90,plain,(
% 1.19/0.53    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)),
% 1.19/0.53    inference(superposition,[],[f35,f32])).
% 1.19/0.53  % SZS output end Proof for theBenchmark
% 1.19/0.53  % (21540)------------------------------
% 1.19/0.53  % (21540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.53  % (21540)Termination reason: Refutation
% 1.19/0.53  
% 1.19/0.53  % (21540)Memory used [KB]: 6268
% 1.19/0.53  % (21540)Time elapsed: 0.100 s
% 1.19/0.53  % (21540)------------------------------
% 1.19/0.53  % (21540)------------------------------
% 1.19/0.53  % (21535)Success in time 0.159 s
%------------------------------------------------------------------------------
