%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:19 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 350 expanded)
%              Number of leaves         :   23 ( 105 expanded)
%              Depth                    :   22
%              Number of atoms          :  346 ( 999 expanded)
%              Number of equality atoms :  100 ( 430 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f538,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f60,f64,f80,f83,f291,f299,f304,f308,f314,f315,f508,f530,f537])).

fof(f537,plain,
    ( ~ spl1_6
    | spl1_28 ),
    inference(avatar_split_clause,[],[f536,f528,f70])).

fof(f70,plain,
    ( spl1_6
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f528,plain,
    ( spl1_28
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f536,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl1_28 ),
    inference(resolution,[],[f529,f119])).

fof(f119,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f74,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0) ) ),
    inference(forward_demodulation,[],[f114,f43])).

fof(f43,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0) ) ),
    inference(resolution,[],[f87,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f35,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f74,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f47,f43])).

fof(f47,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f529,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_28 ),
    inference(avatar_component_clause,[],[f528])).

fof(f530,plain,
    ( ~ spl1_28
    | spl1_11
    | ~ spl1_12
    | ~ spl1_20 ),
    inference(avatar_split_clause,[],[f526,f404,f312,f306,f528])).

fof(f306,plain,
    ( spl1_11
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f312,plain,
    ( spl1_12
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f404,plain,
    ( spl1_20
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f526,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl1_11
    | ~ spl1_12
    | ~ spl1_20 ),
    inference(forward_demodulation,[],[f525,f405])).

fof(f405,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f404])).

fof(f525,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl1_11
    | ~ spl1_12 ),
    inference(superposition,[],[f307,f313])).

fof(f313,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f312])).

fof(f307,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_11 ),
    inference(avatar_component_clause,[],[f306])).

fof(f508,plain,
    ( spl1_20
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f507,f312,f297,f404])).

fof(f297,plain,
    ( spl1_9
  <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f507,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f506,f475])).

fof(f475,plain,
    ( ! [X31] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X31,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f383,f313])).

fof(f383,plain,
    ( ! [X31] : k1_xboole_0 = k1_relset_1(k1_xboole_0,X31,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sK0)))))
    | ~ spl1_9 ),
    inference(resolution,[],[f298,f151])).

fof(f151,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X4))))) ) ),
    inference(forward_demodulation,[],[f149,f43])).

fof(f149,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X4)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) ) ),
    inference(resolution,[],[f131,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f35,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f131,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4)))) ) ),
    inference(forward_demodulation,[],[f129,f43])).

fof(f129,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) ) ),
    inference(resolution,[],[f127,f89])).

fof(f127,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4))) ) ),
    inference(forward_demodulation,[],[f125,f43])).

fof(f125,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) ) ),
    inference(resolution,[],[f123,f89])).

fof(f123,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4)) ) ),
    inference(forward_demodulation,[],[f121,f43])).

fof(f121,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) ) ),
    inference(resolution,[],[f118,f89])).

fof(f298,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f297])).

fof(f506,plain,
    ( ! [X45] : k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X45,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))))
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f395,f313])).

fof(f395,plain,
    ( ! [X45] : k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X45,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sK0))))))
    | ~ spl1_9 ),
    inference(resolution,[],[f298,f204])).

fof(f204,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X4)))))) ) ),
    inference(forward_demodulation,[],[f202,f43])).

fof(f202,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X4))))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) ) ),
    inference(resolution,[],[f165,f89])).

fof(f165,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4))))) ) ),
    inference(forward_demodulation,[],[f163,f43])).

fof(f163,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4)))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) ) ),
    inference(resolution,[],[f139,f89])).

fof(f139,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4)))) ) ),
    inference(forward_demodulation,[],[f137,f43])).

fof(f137,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4))))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) ) ),
    inference(resolution,[],[f109,f89])).

fof(f109,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4))) ) ),
    inference(forward_demodulation,[],[f107,f43])).

fof(f107,plain,(
    ! [X4,X5,X3] :
      ( k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5))) ) ),
    inference(resolution,[],[f96,f89])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1)) ) ),
    inference(forward_demodulation,[],[f94,f43])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(resolution,[],[f93,f35])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f91,f43])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relat_1(X0) ) ),
    inference(resolution,[],[f90,f28])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f89,f29])).

fof(f315,plain,
    ( k1_xboole_0 != sK0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f314,plain,
    ( spl1_12
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f309,f302,f312])).

fof(f302,plain,
    ( spl1_10
  <=> r1_tarski(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f309,plain,
    ( k1_xboole_0 = sK0
    | ~ spl1_10 ),
    inference(resolution,[],[f303,f28])).

fof(f303,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f302])).

fof(f308,plain,
    ( ~ spl1_11
    | spl1_2
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f294,f289,f53,f306])).

fof(f53,plain,
    ( spl1_2
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f289,plain,
    ( spl1_8
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f294,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)
    | spl1_2
    | ~ spl1_8 ),
    inference(superposition,[],[f54,f290])).

fof(f290,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f289])).

fof(f54,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f304,plain,
    ( spl1_10
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f300,f289,f78,f302])).

fof(f78,plain,
    ( spl1_7
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f300,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f293,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f293,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))
    | ~ spl1_7
    | ~ spl1_8 ),
    inference(superposition,[],[f79,f290])).

fof(f79,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f299,plain,
    ( spl1_9
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f295,f289,f56,f297])).

fof(f56,plain,
    ( spl1_3
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f295,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(forward_demodulation,[],[f292,f42])).

fof(f292,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)))
    | ~ spl1_3
    | ~ spl1_8 ),
    inference(superposition,[],[f82,f290])).

fof(f82,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f291,plain,
    ( spl1_2
    | spl1_8
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f284,f56,f289,f53])).

fof(f284,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl1_3 ),
    inference(resolution,[],[f283,f82])).

fof(f283,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
      | k1_xboole_0 = X1
      | v1_funct_2(X0,k1_relat_1(X0),X1) ) ),
    inference(equality_resolution,[],[f242])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f38,f34])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,
    ( spl1_3
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f81,f78,f56])).

fof(f81,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl1_7 ),
    inference(resolution,[],[f79,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f80,plain,
    ( spl1_7
    | ~ spl1_4 ),
    inference(avatar_split_clause,[],[f76,f62,f78])).

fof(f62,plain,
    ( spl1_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f76,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_4 ),
    inference(resolution,[],[f27,f63])).

fof(f63,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f64,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f24,f62])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
      | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) )
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          | ~ v1_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
        | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
        | ~ v1_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f60,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f25,f50])).

fof(f50,plain,
    ( spl1_1
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f25,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,
    ( ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f26,f56,f53,f50])).

fof(f26,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : run_vampire %s %d
% 0.08/0.26  % Computer   : n021.cluster.edu
% 0.08/0.26  % Model      : x86_64 x86_64
% 0.08/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.26  % Memory     : 8042.1875MB
% 0.08/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.26  % CPULimit   : 60
% 0.08/0.26  % WCLimit    : 600
% 0.08/0.26  % DateTime   : Tue Dec  1 16:23:04 EST 2020
% 0.08/0.26  % CPUTime    : 
% 0.12/0.38  % (3583)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.12/0.38  % (3583)Refutation not found, incomplete strategy% (3583)------------------------------
% 0.12/0.38  % (3583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.39  % (3591)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.12/0.39  % (3583)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.39  
% 0.12/0.39  % (3583)Memory used [KB]: 6140
% 0.12/0.39  % (3583)Time elapsed: 0.061 s
% 0.12/0.39  % (3583)------------------------------
% 0.12/0.39  % (3583)------------------------------
% 0.12/0.40  % (3591)Refutation not found, incomplete strategy% (3591)------------------------------
% 0.12/0.40  % (3591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.40  % (3591)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.40  
% 0.12/0.40  % (3591)Memory used [KB]: 10490
% 0.12/0.40  % (3591)Time elapsed: 0.065 s
% 0.12/0.40  % (3591)------------------------------
% 0.12/0.40  % (3591)------------------------------
% 0.12/0.40  % (3576)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.12/0.41  % (3575)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.12/0.41  % (3585)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.12/0.42  % (3584)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.12/0.42  % (3584)Refutation not found, incomplete strategy% (3584)------------------------------
% 0.12/0.42  % (3584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.42  % (3584)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.42  
% 0.12/0.42  % (3584)Memory used [KB]: 1663
% 0.12/0.42  % (3584)Time elapsed: 0.076 s
% 0.12/0.42  % (3584)------------------------------
% 0.12/0.42  % (3584)------------------------------
% 0.12/0.43  % (3576)Refutation found. Thanks to Tanya!
% 0.12/0.43  % SZS status Theorem for theBenchmark
% 0.12/0.43  % SZS output start Proof for theBenchmark
% 0.12/0.43  fof(f538,plain,(
% 0.12/0.43    $false),
% 0.12/0.43    inference(avatar_sat_refutation,[],[f58,f60,f64,f80,f83,f291,f299,f304,f308,f314,f315,f508,f530,f537])).
% 0.12/0.43  fof(f537,plain,(
% 0.12/0.43    ~spl1_6 | spl1_28),
% 0.12/0.43    inference(avatar_split_clause,[],[f536,f528,f70])).
% 0.12/0.43  fof(f70,plain,(
% 0.12/0.43    spl1_6 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.12/0.43  fof(f528,plain,(
% 0.12/0.43    spl1_28 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.12/0.43  fof(f536,plain,(
% 0.12/0.43    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl1_28),
% 0.12/0.43    inference(resolution,[],[f529,f119])).
% 0.12/0.43  fof(f119,plain,(
% 0.12/0.43    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 0.12/0.43    inference(subsumption_resolution,[],[f74,f118])).
% 0.12/0.43  fof(f118,plain,(
% 0.12/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0)) )),
% 0.12/0.43    inference(forward_demodulation,[],[f114,f43])).
% 0.12/0.43  fof(f43,plain,(
% 0.12/0.43    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.12/0.43    inference(equality_resolution,[],[f32])).
% 0.12/0.43  fof(f32,plain,(
% 0.12/0.43    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.12/0.43    inference(cnf_transformation,[],[f22])).
% 0.12/0.43  fof(f22,plain,(
% 0.12/0.43    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.12/0.43    inference(flattening,[],[f21])).
% 0.12/0.43  fof(f21,plain,(
% 0.12/0.43    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.12/0.43    inference(nnf_transformation,[],[f2])).
% 0.12/0.43  fof(f2,axiom,(
% 0.12/0.43    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.12/0.43  fof(f114,plain,(
% 0.12/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X0)) )),
% 0.12/0.43    inference(resolution,[],[f87,f28])).
% 0.12/0.43  fof(f28,plain,(
% 0.12/0.43    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.12/0.43    inference(cnf_transformation,[],[f13])).
% 0.12/0.43  fof(f13,plain,(
% 0.12/0.43    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.12/0.43    inference(ennf_transformation,[],[f1])).
% 0.12/0.43  fof(f1,axiom,(
% 0.12/0.43    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.12/0.43  fof(f87,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (r1_tarski(k1_relset_1(X1,X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.12/0.43    inference(resolution,[],[f35,f29])).
% 0.12/0.43  fof(f29,plain,(
% 0.12/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.12/0.43    inference(cnf_transformation,[],[f20])).
% 0.12/0.43  fof(f20,plain,(
% 0.12/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.12/0.43    inference(nnf_transformation,[],[f3])).
% 0.12/0.43  fof(f3,axiom,(
% 0.12/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.12/0.43  fof(f35,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(cnf_transformation,[],[f15])).
% 0.12/0.43  fof(f15,plain,(
% 0.12/0.43    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.43    inference(ennf_transformation,[],[f5])).
% 0.12/0.43  fof(f5,axiom,(
% 0.12/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.12/0.43  fof(f74,plain,(
% 0.12/0.43    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.12/0.43    inference(forward_demodulation,[],[f47,f43])).
% 0.12/0.43  fof(f47,plain,(
% 0.12/0.43    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.12/0.43    inference(equality_resolution,[],[f39])).
% 0.12/0.43  fof(f39,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(cnf_transformation,[],[f23])).
% 0.12/0.43  fof(f23,plain,(
% 0.12/0.43    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.43    inference(nnf_transformation,[],[f17])).
% 0.12/0.43  fof(f17,plain,(
% 0.12/0.43    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.43    inference(flattening,[],[f16])).
% 0.12/0.43  fof(f16,plain,(
% 0.12/0.43    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.43    inference(ennf_transformation,[],[f7])).
% 0.12/0.43  fof(f7,axiom,(
% 0.12/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.12/0.43  fof(f529,plain,(
% 0.12/0.43    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl1_28),
% 0.12/0.43    inference(avatar_component_clause,[],[f528])).
% 0.12/0.43  fof(f530,plain,(
% 0.12/0.43    ~spl1_28 | spl1_11 | ~spl1_12 | ~spl1_20),
% 0.12/0.43    inference(avatar_split_clause,[],[f526,f404,f312,f306,f528])).
% 0.12/0.43  fof(f306,plain,(
% 0.12/0.43    spl1_11 <=> v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.12/0.43  fof(f312,plain,(
% 0.12/0.43    spl1_12 <=> k1_xboole_0 = sK0),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.12/0.43  fof(f404,plain,(
% 0.12/0.43    spl1_20 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.12/0.43  fof(f526,plain,(
% 0.12/0.43    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl1_11 | ~spl1_12 | ~spl1_20)),
% 0.12/0.43    inference(forward_demodulation,[],[f525,f405])).
% 0.12/0.43  fof(f405,plain,(
% 0.12/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_20),
% 0.12/0.43    inference(avatar_component_clause,[],[f404])).
% 0.12/0.43  fof(f525,plain,(
% 0.12/0.43    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl1_11 | ~spl1_12)),
% 0.12/0.43    inference(superposition,[],[f307,f313])).
% 0.12/0.43  fof(f313,plain,(
% 0.12/0.43    k1_xboole_0 = sK0 | ~spl1_12),
% 0.12/0.43    inference(avatar_component_clause,[],[f312])).
% 0.12/0.43  fof(f307,plain,(
% 0.12/0.43    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | spl1_11),
% 0.12/0.43    inference(avatar_component_clause,[],[f306])).
% 0.12/0.43  fof(f508,plain,(
% 0.12/0.43    spl1_20 | ~spl1_9 | ~spl1_12),
% 0.12/0.43    inference(avatar_split_clause,[],[f507,f312,f297,f404])).
% 0.12/0.43  fof(f297,plain,(
% 0.12/0.43    spl1_9 <=> m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.12/0.43  fof(f507,plain,(
% 0.12/0.43    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl1_9 | ~spl1_12)),
% 0.12/0.43    inference(forward_demodulation,[],[f506,f475])).
% 0.12/0.43  fof(f475,plain,(
% 0.12/0.43    ( ! [X31] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X31,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0)))))) ) | (~spl1_9 | ~spl1_12)),
% 0.12/0.43    inference(forward_demodulation,[],[f383,f313])).
% 0.12/0.43  fof(f383,plain,(
% 0.12/0.43    ( ! [X31] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X31,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sK0)))))) ) | ~spl1_9),
% 0.12/0.43    inference(resolution,[],[f298,f151])).
% 0.12/0.43  fof(f151,plain,(
% 0.12/0.43    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X4)))))) )),
% 0.12/0.43    inference(forward_demodulation,[],[f149,f43])).
% 0.12/0.43  fof(f149,plain,(
% 0.12/0.43    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X4))))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) )),
% 0.12/0.43    inference(resolution,[],[f131,f89])).
% 0.12/0.43  fof(f89,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(duplicate_literal_removal,[],[f88])).
% 0.12/0.43  fof(f88,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(superposition,[],[f35,f34])).
% 0.12/0.43  fof(f34,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(cnf_transformation,[],[f14])).
% 0.12/0.43  fof(f14,plain,(
% 0.12/0.43    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.12/0.43    inference(ennf_transformation,[],[f6])).
% 0.12/0.43  fof(f6,axiom,(
% 0.12/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.12/0.43  fof(f131,plain,(
% 0.12/0.43    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4))))) )),
% 0.12/0.43    inference(forward_demodulation,[],[f129,f43])).
% 0.12/0.43  fof(f129,plain,(
% 0.12/0.43    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) )),
% 0.12/0.43    inference(resolution,[],[f127,f89])).
% 0.12/0.43  fof(f127,plain,(
% 0.12/0.43    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4)))) )),
% 0.12/0.43    inference(forward_demodulation,[],[f125,f43])).
% 0.12/0.43  fof(f125,plain,(
% 0.12/0.43    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) )),
% 0.12/0.43    inference(resolution,[],[f123,f89])).
% 0.12/0.43  fof(f123,plain,(
% 0.12/0.43    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4))) )),
% 0.12/0.43    inference(forward_demodulation,[],[f121,f43])).
% 0.12/0.43  fof(f121,plain,(
% 0.12/0.43    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) )),
% 0.12/0.43    inference(resolution,[],[f118,f89])).
% 0.12/0.43  fof(f298,plain,(
% 0.12/0.43    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~spl1_9),
% 0.12/0.43    inference(avatar_component_clause,[],[f297])).
% 0.12/0.43  fof(f506,plain,(
% 0.12/0.43    ( ! [X45] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X45,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(k1_xboole_0))))))) ) | (~spl1_9 | ~spl1_12)),
% 0.12/0.43    inference(forward_demodulation,[],[f395,f313])).
% 0.12/0.43  fof(f395,plain,(
% 0.12/0.43    ( ! [X45] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X45,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(sK0))))))) ) | ~spl1_9),
% 0.12/0.43    inference(resolution,[],[f298,f204])).
% 0.12/0.43  fof(f204,plain,(
% 0.12/0.43    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X4))))))) )),
% 0.12/0.43    inference(forward_demodulation,[],[f202,f43])).
% 0.12/0.43  fof(f202,plain,(
% 0.12/0.43    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(k1_relat_1(X4)))))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) )),
% 0.12/0.43    inference(resolution,[],[f165,f89])).
% 0.12/0.43  fof(f165,plain,(
% 0.12/0.43    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4)))))) )),
% 0.12/0.43    inference(forward_demodulation,[],[f163,f43])).
% 0.12/0.43  fof(f163,plain,(
% 0.12/0.43    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(k1_relat_1(X4))))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) )),
% 0.12/0.43    inference(resolution,[],[f139,f89])).
% 0.12/0.43  fof(f139,plain,(
% 0.12/0.43    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4))))) )),
% 0.12/0.43    inference(forward_demodulation,[],[f137,f43])).
% 0.12/0.43  fof(f137,plain,(
% 0.12/0.43    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(k1_relat_1(X4)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) )),
% 0.12/0.43    inference(resolution,[],[f109,f89])).
% 0.12/0.43  fof(f109,plain,(
% 0.12/0.43    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4)))) )),
% 0.12/0.43    inference(forward_demodulation,[],[f107,f43])).
% 0.12/0.43  fof(f107,plain,(
% 0.12/0.43    ( ! [X4,X5,X3] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X3,k1_relat_1(X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))) )),
% 0.12/0.43    inference(resolution,[],[f96,f89])).
% 0.12/0.43  fof(f96,plain,(
% 0.12/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1))) )),
% 0.12/0.43    inference(forward_demodulation,[],[f94,f43])).
% 0.12/0.43  fof(f94,plain,(
% 0.12/0.43    ( ! [X0,X1] : (k1_xboole_0 = k1_relat_1(k1_relset_1(k1_xboole_0,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 0.12/0.43    inference(resolution,[],[f93,f35])).
% 0.12/0.43  fof(f93,plain,(
% 0.12/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.12/0.43    inference(forward_demodulation,[],[f91,f43])).
% 0.12/0.43  fof(f91,plain,(
% 0.12/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relat_1(X0)) )),
% 0.12/0.43    inference(resolution,[],[f90,f28])).
% 0.12/0.43  fof(f90,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.12/0.43    inference(resolution,[],[f89,f29])).
% 0.12/0.43  fof(f315,plain,(
% 0.12/0.43    k1_xboole_0 != sK0 | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))),
% 0.12/0.43    introduced(theory_tautology_sat_conflict,[])).
% 0.12/0.43  fof(f314,plain,(
% 0.12/0.43    spl1_12 | ~spl1_10),
% 0.12/0.43    inference(avatar_split_clause,[],[f309,f302,f312])).
% 0.12/0.43  fof(f302,plain,(
% 0.12/0.43    spl1_10 <=> r1_tarski(sK0,k1_xboole_0)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.12/0.43  fof(f309,plain,(
% 0.12/0.43    k1_xboole_0 = sK0 | ~spl1_10),
% 0.12/0.43    inference(resolution,[],[f303,f28])).
% 0.12/0.43  fof(f303,plain,(
% 0.12/0.43    r1_tarski(sK0,k1_xboole_0) | ~spl1_10),
% 0.12/0.43    inference(avatar_component_clause,[],[f302])).
% 0.12/0.43  fof(f308,plain,(
% 0.12/0.43    ~spl1_11 | spl1_2 | ~spl1_8),
% 0.12/0.43    inference(avatar_split_clause,[],[f294,f289,f53,f306])).
% 0.12/0.43  fof(f53,plain,(
% 0.12/0.43    spl1_2 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.12/0.43  fof(f289,plain,(
% 0.12/0.43    spl1_8 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.12/0.43  fof(f294,plain,(
% 0.12/0.43    ~v1_funct_2(sK0,k1_relat_1(sK0),k1_xboole_0) | (spl1_2 | ~spl1_8)),
% 0.12/0.43    inference(superposition,[],[f54,f290])).
% 0.12/0.43  fof(f290,plain,(
% 0.12/0.43    k1_xboole_0 = k2_relat_1(sK0) | ~spl1_8),
% 0.12/0.43    inference(avatar_component_clause,[],[f289])).
% 0.12/0.43  fof(f54,plain,(
% 0.12/0.43    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl1_2),
% 0.12/0.43    inference(avatar_component_clause,[],[f53])).
% 0.12/0.43  fof(f304,plain,(
% 0.12/0.43    spl1_10 | ~spl1_7 | ~spl1_8),
% 0.12/0.43    inference(avatar_split_clause,[],[f300,f289,f78,f302])).
% 0.12/0.43  fof(f78,plain,(
% 0.12/0.43    spl1_7 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.12/0.43  fof(f300,plain,(
% 0.12/0.43    r1_tarski(sK0,k1_xboole_0) | (~spl1_7 | ~spl1_8)),
% 0.12/0.43    inference(forward_demodulation,[],[f293,f42])).
% 0.12/0.43  fof(f42,plain,(
% 0.12/0.43    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.12/0.43    inference(equality_resolution,[],[f33])).
% 0.12/0.43  fof(f33,plain,(
% 0.12/0.43    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.12/0.43    inference(cnf_transformation,[],[f22])).
% 0.12/0.43  fof(f293,plain,(
% 0.12/0.43    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0)) | (~spl1_7 | ~spl1_8)),
% 0.12/0.43    inference(superposition,[],[f79,f290])).
% 0.12/0.43  fof(f79,plain,(
% 0.12/0.43    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_7),
% 0.12/0.43    inference(avatar_component_clause,[],[f78])).
% 0.12/0.43  fof(f299,plain,(
% 0.12/0.43    spl1_9 | ~spl1_3 | ~spl1_8),
% 0.12/0.43    inference(avatar_split_clause,[],[f295,f289,f56,f297])).
% 0.12/0.43  fof(f56,plain,(
% 0.12/0.43    spl1_3 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.12/0.43  fof(f295,plain,(
% 0.12/0.43    m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | (~spl1_3 | ~spl1_8)),
% 0.12/0.43    inference(forward_demodulation,[],[f292,f42])).
% 0.12/0.43  fof(f292,plain,(
% 0.12/0.43    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k1_xboole_0))) | (~spl1_3 | ~spl1_8)),
% 0.12/0.43    inference(superposition,[],[f82,f290])).
% 0.12/0.43  fof(f82,plain,(
% 0.12/0.43    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl1_3),
% 0.12/0.43    inference(avatar_component_clause,[],[f56])).
% 0.12/0.43  fof(f291,plain,(
% 0.12/0.43    spl1_2 | spl1_8 | ~spl1_3),
% 0.12/0.43    inference(avatar_split_clause,[],[f284,f56,f289,f53])).
% 0.12/0.43  fof(f284,plain,(
% 0.12/0.43    k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl1_3),
% 0.12/0.43    inference(resolution,[],[f283,f82])).
% 0.12/0.43  fof(f283,plain,(
% 0.12/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) | k1_xboole_0 = X1 | v1_funct_2(X0,k1_relat_1(X0),X1)) )),
% 0.12/0.43    inference(equality_resolution,[],[f242])).
% 0.12/0.43  fof(f242,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(duplicate_literal_removal,[],[f241])).
% 0.12/0.43  fof(f241,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(superposition,[],[f38,f34])).
% 0.12/0.43  fof(f38,plain,(
% 0.12/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.12/0.43    inference(cnf_transformation,[],[f23])).
% 0.12/0.43  fof(f83,plain,(
% 0.12/0.43    spl1_3 | ~spl1_7),
% 0.12/0.43    inference(avatar_split_clause,[],[f81,f78,f56])).
% 0.12/0.43  fof(f81,plain,(
% 0.12/0.43    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl1_7),
% 0.12/0.43    inference(resolution,[],[f79,f30])).
% 0.12/0.43  fof(f30,plain,(
% 0.12/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.12/0.43    inference(cnf_transformation,[],[f20])).
% 0.12/0.43  fof(f80,plain,(
% 0.12/0.43    spl1_7 | ~spl1_4),
% 0.12/0.43    inference(avatar_split_clause,[],[f76,f62,f78])).
% 0.12/0.43  fof(f62,plain,(
% 0.12/0.43    spl1_4 <=> v1_relat_1(sK0)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.12/0.43  fof(f76,plain,(
% 0.12/0.43    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_4),
% 0.12/0.43    inference(resolution,[],[f27,f63])).
% 0.12/0.43  fof(f63,plain,(
% 0.12/0.43    v1_relat_1(sK0) | ~spl1_4),
% 0.12/0.43    inference(avatar_component_clause,[],[f62])).
% 0.12/0.43  fof(f27,plain,(
% 0.12/0.43    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.12/0.43    inference(cnf_transformation,[],[f12])).
% 0.12/0.43  fof(f12,plain,(
% 0.12/0.43    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.12/0.43    inference(ennf_transformation,[],[f4])).
% 0.12/0.43  fof(f4,axiom,(
% 0.12/0.43    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.12/0.43  fof(f64,plain,(
% 0.12/0.43    spl1_4),
% 0.12/0.43    inference(avatar_split_clause,[],[f24,f62])).
% 0.12/0.43  fof(f24,plain,(
% 0.12/0.43    v1_relat_1(sK0)),
% 0.12/0.43    inference(cnf_transformation,[],[f19])).
% 0.12/0.43  fof(f19,plain,(
% 0.12/0.43    (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.12/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f18])).
% 0.12/0.43  fof(f18,plain,(
% 0.12/0.43    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => ((~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.12/0.43    introduced(choice_axiom,[])).
% 0.12/0.43  fof(f11,plain,(
% 0.12/0.43    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.12/0.43    inference(flattening,[],[f10])).
% 0.12/0.43  fof(f10,plain,(
% 0.12/0.43    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.12/0.43    inference(ennf_transformation,[],[f9])).
% 0.12/0.43  fof(f9,negated_conjecture,(
% 0.12/0.43    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.12/0.43    inference(negated_conjecture,[],[f8])).
% 0.12/0.43  fof(f8,conjecture,(
% 0.12/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.12/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.12/0.43  fof(f60,plain,(
% 0.12/0.43    spl1_1),
% 0.12/0.43    inference(avatar_split_clause,[],[f25,f50])).
% 0.12/0.43  fof(f50,plain,(
% 0.12/0.43    spl1_1 <=> v1_funct_1(sK0)),
% 0.12/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.12/0.43  fof(f25,plain,(
% 0.12/0.43    v1_funct_1(sK0)),
% 0.12/0.43    inference(cnf_transformation,[],[f19])).
% 0.12/0.43  fof(f58,plain,(
% 0.12/0.43    ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.12/0.43    inference(avatar_split_clause,[],[f26,f56,f53,f50])).
% 0.12/0.43  fof(f26,plain,(
% 0.12/0.43    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.12/0.43    inference(cnf_transformation,[],[f19])).
% 0.12/0.43  % SZS output end Proof for theBenchmark
% 0.12/0.43  % (3576)------------------------------
% 0.12/0.43  % (3576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.43  % (3576)Termination reason: Refutation
% 0.12/0.43  
% 0.12/0.43  % (3576)Memory used [KB]: 10874
% 0.12/0.43  % (3576)Time elapsed: 0.042 s
% 0.12/0.43  % (3576)------------------------------
% 0.12/0.43  % (3576)------------------------------
% 0.12/0.43  % (3564)Success in time 0.161 s
%------------------------------------------------------------------------------
