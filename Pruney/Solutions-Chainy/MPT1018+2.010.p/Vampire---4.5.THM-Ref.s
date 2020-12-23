%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 212 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :  286 (1119 expanded)
%              Number of equality atoms :   56 ( 261 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f97,f132])).

fof(f132,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f130,f18])).

fof(f18,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f130,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f129,f56])).

fof(f56,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f54,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(superposition,[],[f53,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f53,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f52,f22])).

fof(f22,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f52,plain,
    ( ~ v1_funct_1(sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(subsumption_resolution,[],[f50,f23])).

fof(f23,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f50,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | sK0 = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f24,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f129,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f128,f51])).

fof(f51,plain,(
    v1_relat_1(sK1) ),
    inference(resolution,[],[f24,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f128,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f127,f64])).

fof(f64,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_1
  <=> v1_funct_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f127,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f126,f68])).

fof(f68,plain,
    ( v1_relat_1(k2_funct_1(sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl6_2
  <=> v1_relat_1(k2_funct_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f126,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f125,f25])).

fof(f25,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f125,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f124,f22])).

fof(f124,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f110,f21])).

fof(f21,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f110,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK2,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_4 ),
    inference(superposition,[],[f47,f96])).

fof(f96,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_4
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f47,plain,(
    ! [X0,X3] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | k1_funct_1(X1,X2) = X3
      | k2_funct_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).

fof(f97,plain,
    ( ~ spl6_2
    | spl6_4
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f92,f63,f94,f67])).

fof(f92,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f91,f19])).

fof(f19,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f91,plain,
    ( ~ r2_hidden(sK3,sK0)
    | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f90,f56])).

fof(f90,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f89,f51])).

fof(f89,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f88,f64])).

fof(f88,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f87,f25])).

fof(f87,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f78,f22])).

fof(f78,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(k2_funct_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK1))
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f47,f20])).

fof(f20,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f86,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f84,f51])).

fof(f84,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f83,f22])).

fof(f83,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_2 ),
    inference(resolution,[],[f69,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f69,plain,
    ( ~ v1_relat_1(k2_funct_1(sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f82,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f80,f51])).

fof(f80,plain,
    ( ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f79,f22])).

fof(f79,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | spl6_1 ),
    inference(resolution,[],[f65,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,
    ( ~ v1_funct_1(k2_funct_1(sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:27:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (32240)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.45  % (32240)Refutation not found, incomplete strategy% (32240)------------------------------
% 0.21/0.45  % (32240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (32240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (32240)Memory used [KB]: 6140
% 0.21/0.45  % (32240)Time elapsed: 0.035 s
% 0.21/0.45  % (32240)------------------------------
% 0.21/0.45  % (32240)------------------------------
% 0.21/0.47  % (32234)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (32242)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (32235)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (32232)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (32246)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (32231)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (32251)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (32231)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (32241)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (32251)Refutation not found, incomplete strategy% (32251)------------------------------
% 0.21/0.48  % (32251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (32233)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (32251)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (32251)Memory used [KB]: 10618
% 0.21/0.48  % (32251)Time elapsed: 0.078 s
% 0.21/0.48  % (32251)------------------------------
% 0.21/0.48  % (32251)------------------------------
% 0.21/0.48  % (32230)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (32247)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (32250)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (32249)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f82,f86,f97,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~spl6_1 | ~spl6_2 | ~spl6_4),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    $false | (~spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    r2_hidden(sK2,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.49    inference(negated_conjecture,[],[f6])).
% 0.21/0.49  fof(f6,conjecture,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_2)).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~r2_hidden(sK2,sK0) | (~spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.21/0.49    inference(forward_demodulation,[],[f129,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f54,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.49    inference(superposition,[],[f53,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f52,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    v1_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f50,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f24,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k1_relat_1(sK1)) | (~spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f128,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f24,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl6_1 | ~spl6_2 | ~spl6_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f127,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    v1_funct_1(k2_funct_1(sK1)) | ~spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl6_1 <=> v1_funct_1(k2_funct_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl6_2 | ~spl6_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f126,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    v1_relat_1(k2_funct_1(sK1)) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl6_2 <=> v1_relat_1(k2_funct_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl6_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f125,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    v2_funct_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ~v2_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl6_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f22])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl6_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f110,f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    sK2 != sK3),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    sK2 = sK3 | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK2,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl6_4),
% 0.21/0.49    inference(superposition,[],[f47,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl6_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl6_4 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X3] : (k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X1,k1_funct_1(X0,X3)) = X3 | k2_funct_1(X0) != X1) )),
% 0.21/0.49    inference(equality_resolution,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X3,k1_relat_1(X0)) | k1_funct_1(X0,X3) != X2 | k1_funct_1(X1,X2) = X3 | k2_funct_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0)))) & k1_relat_1(X1) = k2_relat_1(X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : ((! [X1] : ((k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) | (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & ((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | (k1_funct_1(X1,X2) != X3 | ~r2_hidden(X2,k2_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(X0) = X1 <=> (! [X2,X3] : (((k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0)))) & ((k1_funct_1(X1,X2) = X3 & r2_hidden(X2,k2_relat_1(X0))) => (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) & k1_relat_1(X1) = k2_relat_1(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_funct_1)).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    ~spl6_2 | spl6_4 | ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f92,f63,f94,f67])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl6_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    r2_hidden(sK3,sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~r2_hidden(sK3,sK0) | sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_relat_1(k2_funct_1(sK1)) | ~spl6_1),
% 0.21/0.49    inference(forward_demodulation,[],[f90,f56])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_relat_1(k2_funct_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~spl6_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f51])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_relat_1(k2_funct_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~spl6_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f64])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f25])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v2_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f78,f22])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v1_relat_1(k2_funct_1(sK1)) | ~v1_funct_1(k2_funct_1(sK1)) | ~r2_hidden(sK3,k1_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(superposition,[],[f47,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    $false | spl6_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f84,f51])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl6_2),
% 0.21/0.49    inference(subsumption_resolution,[],[f83,f22])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl6_2),
% 0.21/0.49    inference(resolution,[],[f69,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~v1_relat_1(k2_funct_1(sK1)) | spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl6_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    $false | spl6_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f51])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | spl6_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f79,f22])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | spl6_1),
% 0.21/0.49    inference(resolution,[],[f65,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ~v1_funct_1(k2_funct_1(sK1)) | spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (32231)------------------------------
% 0.21/0.49  % (32231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (32231)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (32231)Memory used [KB]: 10618
% 0.21/0.49  % (32231)Time elapsed: 0.066 s
% 0.21/0.49  % (32231)------------------------------
% 0.21/0.49  % (32231)------------------------------
% 0.21/0.49  % (32239)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (32224)Success in time 0.131 s
%------------------------------------------------------------------------------
