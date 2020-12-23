%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:18 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 629 expanded)
%              Number of leaves         :   17 ( 158 expanded)
%              Depth                    :   18
%              Number of atoms          :  359 (3755 expanded)
%              Number of equality atoms :   68 ( 502 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f496,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f98,f160,f264,f481,f494])).

fof(f494,plain,
    ( spl3_2
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f493])).

fof(f493,plain,
    ( $false
    | spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f483,f489])).

fof(f489,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f82,f159])).

fof(f159,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f82,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f483,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f464,f159])).

fof(f464,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(resolution,[],[f207,f196])).

fof(f196,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(resolution,[],[f130,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f130,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f129,f118])).

fof(f118,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f30])).

fof(f30,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f129,plain,(
    m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f61,f38])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f207,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | v1_funct_2(k2_funct_1(sK2),sK1,X1) ) ),
    inference(forward_demodulation,[],[f206,f117])).

fof(f117,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f116,f40])).

fof(f40,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f116,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f59,f38])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f206,plain,(
    ! [X1] :
      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X1)
      | ~ r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(forward_demodulation,[],[f205,f111])).

fof(f111,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f110,f90])).

fof(f90,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f58,f38])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f110,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f109,f36])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f109,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f48,f39])).

fof(f39,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f205,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X1) ) ),
    inference(subsumption_resolution,[],[f204,f93])).

fof(f93,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f92,f90])).

fof(f92,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f91,f36])).

fof(f91,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f42,f39])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f204,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X1)
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f199,f100])).

fof(f100,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f99,f90])).

fof(f99,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f94,f36])).

fof(f94,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f199,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X1)
      | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X1)
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(superposition,[],[f51,f114])).

fof(f114,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f113,f90])).

fof(f113,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f112,f36])).

fof(f112,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f481,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f477,f86])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f477,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f203,f196])).

fof(f203,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    inference(forward_demodulation,[],[f202,f117])).

fof(f202,plain,(
    ! [X0] :
      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0)))
      | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    inference(forward_demodulation,[],[f201,f111])).

fof(f201,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) ) ),
    inference(subsumption_resolution,[],[f200,f93])).

fof(f200,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f198,f100])).

fof(f198,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))
      | ~ v1_funct_1(k2_funct_1(sK2))
      | ~ v1_relat_1(k2_funct_1(sK2)) ) ),
    inference(superposition,[],[f52,f114])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f264,plain,
    ( spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f262,f82])).

fof(f262,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f128,f216])).

fof(f216,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f118,f155])).

fof(f155,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_4
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f128,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f127,f117])).

fof(f127,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f126,f111])).

fof(f126,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f125,f114])).

fof(f125,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f120,f93])).

fof(f120,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f100,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f160,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f151,f157,f153])).

fof(f151,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f150,f37])).

fof(f37,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f150,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f62,f38])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f98,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f96,f90])).

fof(f96,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f95,f36])).

fof(f95,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f94,f78])).

fof(f78,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f84,f80,f76])).

fof(f41,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:25:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.38  ipcrm: permission denied for id (1229029377)
% 0.21/0.38  ipcrm: permission denied for id (1229062146)
% 0.21/0.39  ipcrm: permission denied for id (1229094915)
% 0.21/0.39  ipcrm: permission denied for id (1229127684)
% 0.21/0.39  ipcrm: permission denied for id (1229160453)
% 0.21/0.39  ipcrm: permission denied for id (1228472326)
% 0.21/0.39  ipcrm: permission denied for id (1229193223)
% 0.21/0.39  ipcrm: permission denied for id (1229225992)
% 0.21/0.40  ipcrm: permission denied for id (1229291530)
% 0.21/0.40  ipcrm: permission denied for id (1229324299)
% 0.21/0.40  ipcrm: permission denied for id (1229389837)
% 0.21/0.41  ipcrm: permission denied for id (1229488144)
% 0.21/0.41  ipcrm: permission denied for id (1229619220)
% 0.21/0.42  ipcrm: permission denied for id (1229750295)
% 0.21/0.42  ipcrm: permission denied for id (1229881371)
% 0.21/0.42  ipcrm: permission denied for id (1229946909)
% 0.21/0.42  ipcrm: permission denied for id (1229979678)
% 0.21/0.43  ipcrm: permission denied for id (1230045216)
% 0.21/0.43  ipcrm: permission denied for id (1230110754)
% 0.21/0.43  ipcrm: permission denied for id (1228537891)
% 0.21/0.43  ipcrm: permission denied for id (1228603430)
% 0.21/0.43  ipcrm: permission denied for id (1228636200)
% 0.21/0.44  ipcrm: permission denied for id (1230307371)
% 0.22/0.44  ipcrm: permission denied for id (1230340140)
% 0.22/0.44  ipcrm: permission denied for id (1230405677)
% 0.22/0.44  ipcrm: permission denied for id (1230471215)
% 0.22/0.44  ipcrm: permission denied for id (1230503984)
% 0.22/0.45  ipcrm: permission denied for id (1230602291)
% 0.22/0.45  ipcrm: permission denied for id (1230700598)
% 0.22/0.45  ipcrm: permission denied for id (1230766136)
% 0.22/0.46  ipcrm: permission denied for id (1230897212)
% 0.22/0.46  ipcrm: permission denied for id (1230929981)
% 0.22/0.46  ipcrm: permission denied for id (1230995519)
% 0.22/0.47  ipcrm: permission denied for id (1228701761)
% 0.22/0.47  ipcrm: permission denied for id (1231061058)
% 0.22/0.47  ipcrm: permission denied for id (1231093827)
% 0.22/0.47  ipcrm: permission denied for id (1231126596)
% 0.22/0.47  ipcrm: permission denied for id (1231159365)
% 0.22/0.47  ipcrm: permission denied for id (1231192134)
% 0.22/0.47  ipcrm: permission denied for id (1231224903)
% 0.22/0.47  ipcrm: permission denied for id (1228734536)
% 0.22/0.48  ipcrm: permission denied for id (1231257673)
% 0.22/0.48  ipcrm: permission denied for id (1231323211)
% 0.22/0.48  ipcrm: permission denied for id (1231355980)
% 0.22/0.48  ipcrm: permission denied for id (1231388749)
% 0.22/0.48  ipcrm: permission denied for id (1231487055)
% 0.22/0.49  ipcrm: permission denied for id (1231519824)
% 0.22/0.49  ipcrm: permission denied for id (1231552593)
% 0.22/0.49  ipcrm: permission denied for id (1231585362)
% 0.22/0.49  ipcrm: permission denied for id (1228767317)
% 0.22/0.50  ipcrm: permission denied for id (1231913052)
% 0.22/0.50  ipcrm: permission denied for id (1228800093)
% 0.22/0.50  ipcrm: permission denied for id (1231945822)
% 0.22/0.50  ipcrm: permission denied for id (1228832863)
% 0.22/0.51  ipcrm: permission denied for id (1232011361)
% 0.22/0.51  ipcrm: permission denied for id (1232044130)
% 0.22/0.51  ipcrm: permission denied for id (1228865635)
% 0.22/0.52  ipcrm: permission denied for id (1232175207)
% 0.22/0.52  ipcrm: permission denied for id (1232207976)
% 0.22/0.52  ipcrm: permission denied for id (1232240745)
% 0.22/0.52  ipcrm: permission denied for id (1232273514)
% 0.22/0.52  ipcrm: permission denied for id (1232339052)
% 0.22/0.52  ipcrm: permission denied for id (1232371821)
% 0.22/0.53  ipcrm: permission denied for id (1232470128)
% 0.22/0.53  ipcrm: permission denied for id (1232568435)
% 0.22/0.53  ipcrm: permission denied for id (1228931189)
% 0.22/0.54  ipcrm: permission denied for id (1232666743)
% 0.22/0.54  ipcrm: permission denied for id (1232732281)
% 0.22/0.54  ipcrm: permission denied for id (1232797819)
% 0.22/0.54  ipcrm: permission denied for id (1228963964)
% 0.22/0.55  ipcrm: permission denied for id (1232863358)
% 0.22/0.55  ipcrm: permission denied for id (1232896127)
% 0.41/0.67  % (27672)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.41/0.68  % (27671)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.41/0.68  % (27666)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.41/0.68  % (27663)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.41/0.68  % (27680)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.41/0.68  % (27660)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.41/0.69  % (27659)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.41/0.69  % (27662)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.41/0.69  % (27678)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.41/0.69  % (27669)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.41/0.69  % (27670)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.41/0.70  % (27668)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.41/0.70  % (27682)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.41/0.70  % (27676)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.41/0.70  % (27674)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.41/0.70  % (27664)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.41/0.71  % (27670)Refutation found. Thanks to Tanya!
% 0.41/0.71  % SZS status Theorem for theBenchmark
% 0.41/0.71  % (27683)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.41/0.71  % (27661)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.41/0.71  % (27681)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.41/0.72  % (27677)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.41/0.72  % (27667)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.41/0.72  % (27673)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.41/0.72  % (27684)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.41/0.72  % (27679)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.41/0.72  % (27675)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.41/0.72  % (27685)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.41/0.73  % SZS output start Proof for theBenchmark
% 0.41/0.73  fof(f496,plain,(
% 0.41/0.73    $false),
% 0.41/0.73    inference(avatar_sat_refutation,[],[f87,f98,f160,f264,f481,f494])).
% 0.41/0.73  fof(f494,plain,(
% 0.41/0.73    spl3_2 | ~spl3_5),
% 0.41/0.73    inference(avatar_contradiction_clause,[],[f493])).
% 0.41/0.73  fof(f493,plain,(
% 0.41/0.73    $false | (spl3_2 | ~spl3_5)),
% 0.41/0.73    inference(subsumption_resolution,[],[f483,f489])).
% 0.41/0.73  fof(f489,plain,(
% 0.41/0.73    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl3_2 | ~spl3_5)),
% 0.41/0.73    inference(forward_demodulation,[],[f82,f159])).
% 0.41/0.73  fof(f159,plain,(
% 0.41/0.73    k1_xboole_0 = sK1 | ~spl3_5),
% 0.41/0.73    inference(avatar_component_clause,[],[f157])).
% 0.41/0.73  fof(f157,plain,(
% 0.41/0.73    spl3_5 <=> k1_xboole_0 = sK1),
% 0.41/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.41/0.73  fof(f82,plain,(
% 0.41/0.73    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.41/0.73    inference(avatar_component_clause,[],[f80])).
% 0.41/0.73  fof(f80,plain,(
% 0.41/0.73    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.41/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.41/0.73  fof(f483,plain,(
% 0.41/0.73    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | ~spl3_5),
% 0.41/0.73    inference(forward_demodulation,[],[f464,f159])).
% 0.41/0.73  fof(f464,plain,(
% 0.41/0.73    v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.41/0.73    inference(resolution,[],[f207,f196])).
% 0.41/0.73  fof(f196,plain,(
% 0.41/0.73    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.41/0.73    inference(resolution,[],[f130,f56])).
% 0.41/0.73  fof(f56,plain,(
% 0.41/0.73    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f34])).
% 0.41/0.73  fof(f34,plain,(
% 0.41/0.73    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.41/0.73    inference(nnf_transformation,[],[f2])).
% 0.41/0.73  fof(f2,axiom,(
% 0.41/0.73    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.41/0.73  fof(f130,plain,(
% 0.41/0.73    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 0.41/0.73    inference(forward_demodulation,[],[f129,f118])).
% 0.41/0.73  fof(f118,plain,(
% 0.41/0.73    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.41/0.73    inference(resolution,[],[f60,f38])).
% 0.41/0.73  fof(f38,plain,(
% 0.41/0.73    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.41/0.73    inference(cnf_transformation,[],[f31])).
% 0.41/0.73  fof(f31,plain,(
% 0.41/0.73    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.41/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f30])).
% 0.41/0.73  fof(f30,plain,(
% 0.41/0.73    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.41/0.73    introduced(choice_axiom,[])).
% 0.41/0.73  fof(f15,plain,(
% 0.41/0.73    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.41/0.73    inference(flattening,[],[f14])).
% 0.41/0.73  fof(f14,plain,(
% 0.41/0.73    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.41/0.73    inference(ennf_transformation,[],[f13])).
% 0.41/0.73  fof(f13,negated_conjecture,(
% 0.41/0.73    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.41/0.73    inference(negated_conjecture,[],[f12])).
% 0.41/0.73  fof(f12,conjecture,(
% 0.41/0.73    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.41/0.73  fof(f60,plain,(
% 0.41/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f26])).
% 0.41/0.73  fof(f26,plain,(
% 0.41/0.73    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.41/0.73    inference(ennf_transformation,[],[f7])).
% 0.41/0.73  fof(f7,axiom,(
% 0.41/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.41/0.73  fof(f129,plain,(
% 0.41/0.73    m1_subset_1(k1_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK0))),
% 0.41/0.73    inference(resolution,[],[f61,f38])).
% 0.41/0.73  fof(f61,plain,(
% 0.41/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.41/0.73    inference(cnf_transformation,[],[f27])).
% 0.41/0.73  fof(f27,plain,(
% 0.41/0.73    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.41/0.73    inference(ennf_transformation,[],[f6])).
% 0.41/0.73  fof(f6,axiom,(
% 0.41/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.41/0.73  fof(f207,plain,(
% 0.41/0.73    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | v1_funct_2(k2_funct_1(sK2),sK1,X1)) )),
% 0.41/0.73    inference(forward_demodulation,[],[f206,f117])).
% 0.41/0.73  fof(f117,plain,(
% 0.41/0.73    sK1 = k2_relat_1(sK2)),
% 0.41/0.73    inference(forward_demodulation,[],[f116,f40])).
% 0.41/0.73  fof(f40,plain,(
% 0.41/0.73    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.41/0.73    inference(cnf_transformation,[],[f31])).
% 0.41/0.73  fof(f116,plain,(
% 0.41/0.73    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.41/0.73    inference(resolution,[],[f59,f38])).
% 0.41/0.73  fof(f59,plain,(
% 0.41/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f25])).
% 0.41/0.73  fof(f25,plain,(
% 0.41/0.73    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.41/0.73    inference(ennf_transformation,[],[f8])).
% 0.41/0.73  fof(f8,axiom,(
% 0.41/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.41/0.73  fof(f206,plain,(
% 0.41/0.73    ( ! [X1] : (v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),X1) | ~r1_tarski(k1_relat_1(sK2),X1)) )),
% 0.41/0.73    inference(forward_demodulation,[],[f205,f111])).
% 0.41/0.73  fof(f111,plain,(
% 0.41/0.73    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.41/0.73    inference(subsumption_resolution,[],[f110,f90])).
% 0.41/0.73  fof(f90,plain,(
% 0.41/0.73    v1_relat_1(sK2)),
% 0.41/0.73    inference(resolution,[],[f58,f38])).
% 0.41/0.73  fof(f58,plain,(
% 0.41/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f24])).
% 0.41/0.73  fof(f24,plain,(
% 0.41/0.73    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.41/0.73    inference(ennf_transformation,[],[f5])).
% 0.41/0.73  fof(f5,axiom,(
% 0.41/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.41/0.73  fof(f110,plain,(
% 0.41/0.73    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.41/0.73    inference(subsumption_resolution,[],[f109,f36])).
% 0.41/0.73  fof(f36,plain,(
% 0.41/0.73    v1_funct_1(sK2)),
% 0.41/0.73    inference(cnf_transformation,[],[f31])).
% 0.41/0.73  fof(f109,plain,(
% 0.41/0.73    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.41/0.73    inference(resolution,[],[f48,f39])).
% 0.41/0.73  fof(f39,plain,(
% 0.41/0.73    v2_funct_1(sK2)),
% 0.41/0.73    inference(cnf_transformation,[],[f31])).
% 0.41/0.73  fof(f48,plain,(
% 0.41/0.73    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f21])).
% 0.41/0.73  fof(f21,plain,(
% 0.41/0.73    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.41/0.73    inference(flattening,[],[f20])).
% 0.41/0.73  fof(f20,plain,(
% 0.41/0.73    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.41/0.73    inference(ennf_transformation,[],[f4])).
% 0.41/0.73  fof(f4,axiom,(
% 0.41/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.41/0.73  fof(f205,plain,(
% 0.41/0.73    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X1)) )),
% 0.41/0.73    inference(subsumption_resolution,[],[f204,f93])).
% 0.41/0.73  fof(f93,plain,(
% 0.41/0.73    v1_relat_1(k2_funct_1(sK2))),
% 0.41/0.73    inference(subsumption_resolution,[],[f92,f90])).
% 0.41/0.73  fof(f92,plain,(
% 0.41/0.73    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.41/0.73    inference(subsumption_resolution,[],[f91,f36])).
% 0.41/0.73  fof(f91,plain,(
% 0.41/0.73    v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.41/0.73    inference(resolution,[],[f42,f39])).
% 0.41/0.73  fof(f42,plain,(
% 0.41/0.73    ( ! [X0] : (~v2_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f17])).
% 0.41/0.73  fof(f17,plain,(
% 0.41/0.73    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.41/0.73    inference(flattening,[],[f16])).
% 0.41/0.73  fof(f16,plain,(
% 0.41/0.73    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.41/0.73    inference(ennf_transformation,[],[f3])).
% 0.41/0.73  fof(f3,axiom,(
% 0.41/0.73    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.41/0.73  fof(f204,plain,(
% 0.41/0.73    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X1) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.41/0.73    inference(subsumption_resolution,[],[f199,f100])).
% 0.41/0.73  fof(f100,plain,(
% 0.41/0.73    v1_funct_1(k2_funct_1(sK2))),
% 0.41/0.73    inference(subsumption_resolution,[],[f99,f90])).
% 0.41/0.73  fof(f99,plain,(
% 0.41/0.73    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.41/0.73    inference(subsumption_resolution,[],[f94,f36])).
% 0.41/0.73  fof(f94,plain,(
% 0.41/0.73    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.41/0.73    inference(resolution,[],[f43,f39])).
% 0.41/0.73  fof(f43,plain,(
% 0.41/0.73    ( ! [X0] : (~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f17])).
% 0.41/0.73  fof(f199,plain,(
% 0.41/0.73    ( ! [X1] : (~r1_tarski(k1_relat_1(sK2),X1) | v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),X1) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.41/0.73    inference(superposition,[],[f51,f114])).
% 0.41/0.73  fof(f114,plain,(
% 0.41/0.73    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.41/0.73    inference(subsumption_resolution,[],[f113,f90])).
% 0.41/0.73  fof(f113,plain,(
% 0.41/0.73    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.41/0.73    inference(subsumption_resolution,[],[f112,f36])).
% 0.41/0.73  fof(f112,plain,(
% 0.41/0.73    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.41/0.73    inference(resolution,[],[f49,f39])).
% 0.41/0.73  fof(f49,plain,(
% 0.41/0.73    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f21])).
% 0.41/0.73  fof(f51,plain,(
% 0.41/0.73    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f23])).
% 0.41/0.73  fof(f23,plain,(
% 0.41/0.73    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.41/0.73    inference(flattening,[],[f22])).
% 0.41/0.73  fof(f22,plain,(
% 0.41/0.73    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.41/0.73    inference(ennf_transformation,[],[f11])).
% 0.41/0.73  fof(f11,axiom,(
% 0.41/0.73    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.41/0.73  fof(f481,plain,(
% 0.41/0.73    spl3_3),
% 0.41/0.73    inference(avatar_contradiction_clause,[],[f480])).
% 0.41/0.73  fof(f480,plain,(
% 0.41/0.73    $false | spl3_3),
% 0.41/0.73    inference(subsumption_resolution,[],[f477,f86])).
% 0.41/0.73  fof(f86,plain,(
% 0.41/0.73    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.41/0.73    inference(avatar_component_clause,[],[f84])).
% 0.41/0.73  fof(f84,plain,(
% 0.41/0.73    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.41/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.41/0.73  fof(f477,plain,(
% 0.41/0.73    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.41/0.73    inference(resolution,[],[f203,f196])).
% 0.41/0.73  fof(f203,plain,(
% 0.41/0.73    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) )),
% 0.41/0.73    inference(forward_demodulation,[],[f202,f117])).
% 0.41/0.73  fof(f202,plain,(
% 0.41/0.73    ( ! [X0] : (m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) | ~r1_tarski(k1_relat_1(sK2),X0)) )),
% 0.41/0.73    inference(forward_demodulation,[],[f201,f111])).
% 0.41/0.73  fof(f201,plain,(
% 0.41/0.73    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0)))) )),
% 0.41/0.73    inference(subsumption_resolution,[],[f200,f93])).
% 0.41/0.73  fof(f200,plain,(
% 0.41/0.73    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.41/0.73    inference(subsumption_resolution,[],[f198,f100])).
% 0.41/0.73  fof(f198,plain,(
% 0.41/0.73    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),X0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) )),
% 0.41/0.73    inference(superposition,[],[f52,f114])).
% 0.41/0.73  fof(f52,plain,(
% 0.41/0.73    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f23])).
% 0.41/0.73  fof(f264,plain,(
% 0.41/0.73    spl3_2 | ~spl3_4),
% 0.41/0.73    inference(avatar_contradiction_clause,[],[f263])).
% 0.41/0.73  fof(f263,plain,(
% 0.41/0.73    $false | (spl3_2 | ~spl3_4)),
% 0.41/0.73    inference(subsumption_resolution,[],[f262,f82])).
% 0.41/0.73  fof(f262,plain,(
% 0.41/0.73    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl3_4),
% 0.41/0.73    inference(superposition,[],[f128,f216])).
% 0.41/0.73  fof(f216,plain,(
% 0.41/0.73    sK0 = k1_relat_1(sK2) | ~spl3_4),
% 0.41/0.73    inference(superposition,[],[f118,f155])).
% 0.41/0.73  fof(f155,plain,(
% 0.41/0.73    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_4),
% 0.41/0.73    inference(avatar_component_clause,[],[f153])).
% 0.41/0.73  fof(f153,plain,(
% 0.41/0.73    spl3_4 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.41/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.41/0.73  fof(f128,plain,(
% 0.41/0.73    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.41/0.73    inference(forward_demodulation,[],[f127,f117])).
% 0.41/0.73  fof(f127,plain,(
% 0.41/0.73    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.41/0.73    inference(forward_demodulation,[],[f126,f111])).
% 0.41/0.73  fof(f126,plain,(
% 0.41/0.73    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))),
% 0.41/0.73    inference(forward_demodulation,[],[f125,f114])).
% 0.41/0.73  fof(f125,plain,(
% 0.41/0.73    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 0.41/0.73    inference(subsumption_resolution,[],[f120,f93])).
% 0.41/0.73  fof(f120,plain,(
% 0.41/0.73    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.41/0.73    inference(resolution,[],[f100,f46])).
% 0.41/0.73  fof(f46,plain,(
% 0.41/0.73    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.41/0.73    inference(cnf_transformation,[],[f19])).
% 0.41/0.73  fof(f19,plain,(
% 0.41/0.73    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.41/0.73    inference(flattening,[],[f18])).
% 0.41/0.73  fof(f18,plain,(
% 0.41/0.73    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.41/0.73    inference(ennf_transformation,[],[f10])).
% 0.41/0.73  fof(f10,axiom,(
% 0.41/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.41/0.73  fof(f160,plain,(
% 0.41/0.73    spl3_4 | spl3_5),
% 0.41/0.73    inference(avatar_split_clause,[],[f151,f157,f153])).
% 0.41/0.73  fof(f151,plain,(
% 0.41/0.73    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.41/0.73    inference(subsumption_resolution,[],[f150,f37])).
% 0.41/0.73  fof(f37,plain,(
% 0.41/0.73    v1_funct_2(sK2,sK0,sK1)),
% 0.41/0.73    inference(cnf_transformation,[],[f31])).
% 0.41/0.73  fof(f150,plain,(
% 0.41/0.73    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.41/0.73    inference(resolution,[],[f62,f38])).
% 0.41/0.73  fof(f62,plain,(
% 0.41/0.73    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.41/0.73    inference(cnf_transformation,[],[f35])).
% 0.41/0.73  fof(f35,plain,(
% 0.41/0.73    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.41/0.73    inference(nnf_transformation,[],[f29])).
% 0.41/0.73  fof(f29,plain,(
% 0.41/0.73    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.41/0.73    inference(flattening,[],[f28])).
% 0.41/0.73  fof(f28,plain,(
% 0.41/0.73    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.41/0.73    inference(ennf_transformation,[],[f9])).
% 0.41/0.73  fof(f9,axiom,(
% 0.41/0.73    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.41/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.41/0.73  fof(f98,plain,(
% 0.41/0.73    spl3_1),
% 0.41/0.73    inference(avatar_contradiction_clause,[],[f97])).
% 0.41/0.73  fof(f97,plain,(
% 0.41/0.73    $false | spl3_1),
% 0.41/0.73    inference(subsumption_resolution,[],[f96,f90])).
% 0.41/0.73  fof(f96,plain,(
% 0.41/0.73    ~v1_relat_1(sK2) | spl3_1),
% 0.41/0.73    inference(subsumption_resolution,[],[f95,f36])).
% 0.41/0.73  fof(f95,plain,(
% 0.41/0.73    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_1),
% 0.41/0.73    inference(subsumption_resolution,[],[f94,f78])).
% 0.41/0.73  fof(f78,plain,(
% 0.41/0.73    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.41/0.73    inference(avatar_component_clause,[],[f76])).
% 0.41/0.73  fof(f76,plain,(
% 0.41/0.73    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.41/0.73    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.41/0.73  fof(f87,plain,(
% 0.41/0.73    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.41/0.73    inference(avatar_split_clause,[],[f41,f84,f80,f76])).
% 0.41/0.73  fof(f41,plain,(
% 0.41/0.73    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.41/0.73    inference(cnf_transformation,[],[f31])).
% 0.41/0.73  % SZS output end Proof for theBenchmark
% 0.41/0.73  % (27670)------------------------------
% 0.41/0.73  % (27670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.41/0.73  % (27670)Termination reason: Refutation
% 0.41/0.73  
% 0.41/0.73  % (27670)Memory used [KB]: 10874
% 0.41/0.73  % (27670)Time elapsed: 0.127 s
% 0.41/0.73  % (27670)------------------------------
% 0.41/0.73  % (27670)------------------------------
% 0.41/0.73  % (27479)Success in time 0.351 s
%------------------------------------------------------------------------------
