%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 617 expanded)
%              Number of leaves         :   21 ( 210 expanded)
%              Depth                    :   21
%              Number of atoms          :  509 (5657 expanded)
%              Number of equality atoms :  118 (1468 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f873,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f68,f162,f262,f295,f312,f453,f468,f532,f588,f591,f640,f856,f872])).

fof(f872,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_25
    | spl5_29 ),
    inference(avatar_contradiction_clause,[],[f871])).

fof(f871,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_25
    | spl5_29 ),
    inference(subsumption_resolution,[],[f870,f380])).

fof(f380,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f214,f62])).

fof(f62,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f214,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f29,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f29,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ v2_funct_1(sK4)
      | ~ v2_funct_1(sK3) )
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & sK1 = k2_relset_1(sK0,sK1,sK3)
    & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ v2_funct_1(X4)
              | ~ v2_funct_1(X3) )
            & ( k1_xboole_0 = X1
              | k1_xboole_0 != X2 )
            & k2_relset_1(X0,X1,X3) = X1
            & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(sK3) )
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & sK1 = k2_relset_1(sK0,sK1,sK3)
          & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ( ~ v2_funct_1(X4)
          | ~ v2_funct_1(sK3) )
        & ( k1_xboole_0 = sK1
          | k1_xboole_0 != sK2 )
        & sK1 = k2_relset_1(sK0,sK1,sK3)
        & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X4,sK1,sK2)
        & v1_funct_1(X4) )
   => ( ( ~ v2_funct_1(sK4)
        | ~ v2_funct_1(sK3) )
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & sK1 = k2_relset_1(sK0,sK1,sK3)
      & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X0,X1,X3) = X1
                & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
             => ( ( v2_funct_1(X4)
                  & v2_funct_1(X3) )
                | ( k1_xboole_0 != X1
                  & k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f870,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_25
    | spl5_29 ),
    inference(subsumption_resolution,[],[f864,f452])).

fof(f452,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | spl5_29 ),
    inference(avatar_component_clause,[],[f450])).

fof(f450,plain,
    ( spl5_29
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f864,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_25 ),
    inference(superposition,[],[f42,f353])).

fof(f353,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl5_25
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f856,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_24 ),
    inference(avatar_contradiction_clause,[],[f855])).

fof(f855,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_4
    | spl5_24 ),
    inference(subsumption_resolution,[],[f349,f380])).

fof(f349,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl5_24
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f640,plain,
    ( ~ spl5_24
    | spl5_25
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f632,f65,f61,f351,f347])).

fof(f632,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f334,f50])).

fof(f50,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f334,plain,
    ( v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f164,f62])).

fof(f164,plain,
    ( v1_funct_2(sK4,k1_xboole_0,sK2)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f28,f67])).

fof(f28,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f591,plain,
    ( spl5_3
    | spl5_18 ),
    inference(avatar_split_clause,[],[f590,f146,f61])).

fof(f146,plain,
    ( spl5_18
  <=> sK1 = k1_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f590,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f546,f29])).

fof(f546,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f28,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f588,plain,
    ( spl5_2
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f587])).

fof(f587,plain,
    ( $false
    | spl5_2
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f586,f271])).

fof(f271,plain,(
    sK1 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f269,f26])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f269,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f31,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f31,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f586,plain,
    ( sK1 != k2_relat_1(sK3)
    | spl5_2
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f539,f530])).

fof(f530,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl5_32
  <=> sK1 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f539,plain,
    ( k2_relat_1(sK3) != k1_relat_1(sK4)
    | spl5_2
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f466,f58])).

fof(f58,plain,
    ( ~ v2_funct_1(sK4)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl5_2
  <=> v2_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f466,plain,
    ( v2_funct_1(sK4)
    | k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f465,f103])).

fof(f103,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_10
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f465,plain,
    ( v2_funct_1(sK4)
    | k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f464,f27])).

fof(f27,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f464,plain,
    ( v2_funct_1(sK4)
    | k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f463,f77])).

fof(f77,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f463,plain,
    ( v2_funct_1(sK4)
    | k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f281,f24])).

fof(f24,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f281,plain,
    ( v2_funct_1(sK4)
    | k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f279,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f279,plain,(
    v2_funct_1(k5_relat_1(sK3,sK4)) ),
    inference(subsumption_resolution,[],[f278,f24])).

fof(f278,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f277,f26])).

fof(f277,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f276,f27])).

fof(f276,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f275,f29])).

fof(f275,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f30,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f30,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f22])).

fof(f532,plain,
    ( ~ spl5_17
    | spl5_32
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f304,f146,f528,f142])).

fof(f142,plain,
    ( spl5_17
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f304,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_18 ),
    inference(superposition,[],[f42,f148])).

fof(f148,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f146])).

fof(f468,plain,
    ( spl5_2
    | ~ spl5_29
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f467,f102,f76,f65,f450,f56])).

fof(f467,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | v2_funct_1(sK4)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f466,f331])).

fof(f331,plain,
    ( k1_xboole_0 = k2_relat_1(sK3)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f271,f67])).

fof(f453,plain,
    ( spl5_1
    | ~ spl5_29
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f448,f102,f76,f65,f450,f52])).

fof(f52,plain,
    ( spl5_1
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f448,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | v2_funct_1(sK3)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f447,f331])).

fof(f447,plain,
    ( v2_funct_1(sK3)
    | k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f446,f103])).

fof(f446,plain,
    ( v2_funct_1(sK3)
    | k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f445,f27])).

fof(f445,plain,
    ( v2_funct_1(sK3)
    | k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f444,f77])).

fof(f444,plain,
    ( v2_funct_1(sK3)
    | k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f280,f24])).

fof(f280,plain,
    ( v2_funct_1(sK3)
    | k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f279,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f312,plain,
    ( spl5_1
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | spl5_1
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f310,f29])).

fof(f310,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_1
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_18 ),
    inference(subsumption_resolution,[],[f304,f287])).

fof(f287,plain,
    ( sK1 != k1_relat_1(sK4)
    | spl5_1
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f286,f271])).

fof(f286,plain,
    ( k2_relat_1(sK3) != k1_relat_1(sK4)
    | spl5_1
    | ~ spl5_5
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f285,f103])).

fof(f285,plain,
    ( k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f284,f27])).

fof(f284,plain,
    ( k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_1
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f283,f77])).

fof(f283,plain,
    ( k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f282,f24])).

fof(f282,plain,
    ( k2_relat_1(sK3) != k1_relat_1(sK4)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f280,f54])).

fof(f54,plain,
    ( ~ v2_funct_1(sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f295,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl5_17 ),
    inference(subsumption_resolution,[],[f144,f29])).

fof(f144,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f142])).

fof(f262,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | spl5_10 ),
    inference(subsumption_resolution,[],[f256,f104])).

fof(f104,plain,
    ( ~ v1_relat_1(sK4)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f256,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f29,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f162,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f156,f78])).

fof(f78,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f156,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f26,f45])).

fof(f68,plain,
    ( ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f32,f65,f61])).

fof(f32,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f33,f56,f52])).

fof(f33,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (17458)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (17440)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (17458)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f873,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f59,f68,f162,f262,f295,f312,f453,f468,f532,f588,f591,f640,f856,f872])).
% 0.21/0.50  fof(f872,plain,(
% 0.21/0.50    ~spl5_3 | ~spl5_4 | ~spl5_25 | spl5_29),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f871])).
% 0.21/0.50  fof(f871,plain,(
% 0.21/0.50    $false | (~spl5_3 | ~spl5_4 | ~spl5_25 | spl5_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f870,f380])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(forward_demodulation,[],[f214,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl5_3 <=> k1_xboole_0 = sK2),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~spl5_4),
% 0.21/0.50    inference(forward_demodulation,[],[f29,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | ~spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl5_4 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ((~v2_funct_1(sK4) | ~v2_funct_1(sK3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & sK1 = k2_relset_1(sK0,sK1,sK3) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f21,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(sK3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & sK1 = k2_relset_1(sK0,sK1,sK3) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(sK3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & sK1 = k2_relset_1(sK0,sK1,sK3) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) => ((~v2_funct_1(sK4) | ~v2_funct_1(sK3)) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & sK1 = k2_relset_1(sK0,sK1,sK3) & v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (? [X4] : ((((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2)) & (k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 0.21/0.50  fof(f870,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_25 | spl5_29)),
% 0.21/0.50    inference(subsumption_resolution,[],[f864,f452])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(sK4) | spl5_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f450])).
% 0.21/0.50  fof(f450,plain,(
% 0.21/0.50    spl5_29 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.50  fof(f864,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl5_25),
% 0.21/0.50    inference(superposition,[],[f42,f353])).
% 0.21/0.50  fof(f353,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) | ~spl5_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f351])).
% 0.21/0.50  fof(f351,plain,(
% 0.21/0.50    spl5_25 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f856,plain,(
% 0.21/0.50    ~spl5_3 | ~spl5_4 | spl5_24),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f855])).
% 0.21/0.50  fof(f855,plain,(
% 0.21/0.50    $false | (~spl5_3 | ~spl5_4 | spl5_24)),
% 0.21/0.50    inference(subsumption_resolution,[],[f349,f380])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl5_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f347])).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    spl5_24 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.50  fof(f640,plain,(
% 0.21/0.50    ~spl5_24 | spl5_25 | ~spl5_3 | ~spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f632,f65,f61,f351,f347])).
% 0.21/0.50  fof(f632,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(resolution,[],[f334,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f334,plain,(
% 0.21/0.50    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) | (~spl5_3 | ~spl5_4)),
% 0.21/0.50    inference(forward_demodulation,[],[f164,f62])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    v1_funct_2(sK4,k1_xboole_0,sK2) | ~spl5_4),
% 0.21/0.50    inference(backward_demodulation,[],[f28,f67])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    v1_funct_2(sK4,sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f591,plain,(
% 0.21/0.50    spl5_3 | spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f590,f146,f61])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    spl5_18 <=> sK1 = k1_relset_1(sK1,sK2,sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.50  fof(f590,plain,(
% 0.21/0.50    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 0.21/0.50    inference(subsumption_resolution,[],[f546,f29])).
% 0.21/0.50  fof(f546,plain,(
% 0.21/0.50    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    inference(resolution,[],[f28,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f588,plain,(
% 0.21/0.50    spl5_2 | ~spl5_5 | ~spl5_10 | ~spl5_32),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f587])).
% 0.21/0.50  fof(f587,plain,(
% 0.21/0.50    $false | (spl5_2 | ~spl5_5 | ~spl5_10 | ~spl5_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f586,f271])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f269,f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    sK1 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(superposition,[],[f31,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f586,plain,(
% 0.21/0.50    sK1 != k2_relat_1(sK3) | (spl5_2 | ~spl5_5 | ~spl5_10 | ~spl5_32)),
% 0.21/0.50    inference(forward_demodulation,[],[f539,f530])).
% 0.21/0.50  fof(f530,plain,(
% 0.21/0.50    sK1 = k1_relat_1(sK4) | ~spl5_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f528])).
% 0.21/0.50  fof(f528,plain,(
% 0.21/0.50    spl5_32 <=> sK1 = k1_relat_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.50  fof(f539,plain,(
% 0.21/0.50    k2_relat_1(sK3) != k1_relat_1(sK4) | (spl5_2 | ~spl5_5 | ~spl5_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f466,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ~v2_funct_1(sK4) | spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl5_2 <=> v2_funct_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f466,plain,(
% 0.21/0.50    v2_funct_1(sK4) | k2_relat_1(sK3) != k1_relat_1(sK4) | (~spl5_5 | ~spl5_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f465,f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    v1_relat_1(sK4) | ~spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl5_10 <=> v1_relat_1(sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.50  fof(f465,plain,(
% 0.21/0.50    v2_funct_1(sK4) | k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl5_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f464,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    v1_funct_1(sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f464,plain,(
% 0.21/0.50    v2_funct_1(sK4) | k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~spl5_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f463,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl5_5 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f463,plain,(
% 0.21/0.50    v2_funct_1(sK4) | k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f281,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    v2_funct_1(sK4) | k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.50    inference(resolution,[],[f279,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    v2_funct_1(k5_relat_1(sK3,sK4))),
% 0.21/0.50    inference(subsumption_resolution,[],[f278,f24])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    v2_funct_1(k5_relat_1(sK3,sK4)) | ~v1_funct_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f277,f26])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    v2_funct_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f276,f27])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    v2_funct_1(k5_relat_1(sK3,sK4)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f275,f29])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    v2_funct_1(k5_relat_1(sK3,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)),
% 0.21/0.50    inference(superposition,[],[f30,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f532,plain,(
% 0.21/0.50    ~spl5_17 | spl5_32 | ~spl5_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f304,f146,f528,f142])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl5_17 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.50  fof(f304,plain,(
% 0.21/0.50    sK1 = k1_relat_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_18),
% 0.21/0.50    inference(superposition,[],[f42,f148])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    sK1 = k1_relset_1(sK1,sK2,sK4) | ~spl5_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f146])).
% 0.21/0.50  fof(f468,plain,(
% 0.21/0.50    spl5_2 | ~spl5_29 | ~spl5_4 | ~spl5_5 | ~spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f467,f102,f76,f65,f450,f56])).
% 0.21/0.50  fof(f467,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(sK4) | v2_funct_1(sK4) | (~spl5_4 | ~spl5_5 | ~spl5_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f466,f331])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(sK3) | ~spl5_4),
% 0.21/0.50    inference(backward_demodulation,[],[f271,f67])).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    spl5_1 | ~spl5_29 | ~spl5_4 | ~spl5_5 | ~spl5_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f448,f102,f76,f65,f450,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl5_1 <=> v2_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f448,plain,(
% 0.21/0.50    k1_xboole_0 != k1_relat_1(sK4) | v2_funct_1(sK3) | (~spl5_4 | ~spl5_5 | ~spl5_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f447,f331])).
% 0.21/0.50  fof(f447,plain,(
% 0.21/0.50    v2_funct_1(sK3) | k2_relat_1(sK3) != k1_relat_1(sK4) | (~spl5_5 | ~spl5_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f446,f103])).
% 0.21/0.50  fof(f446,plain,(
% 0.21/0.50    v2_funct_1(sK3) | k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_relat_1(sK4) | ~spl5_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f445,f27])).
% 0.21/0.50  fof(f445,plain,(
% 0.21/0.50    v2_funct_1(sK3) | k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~spl5_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f444,f77])).
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    v2_funct_1(sK3) | k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f280,f24])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    v2_funct_1(sK3) | k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.21/0.50    inference(resolution,[],[f279,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f312,plain,(
% 0.21/0.50    spl5_1 | ~spl5_5 | ~spl5_10 | ~spl5_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f311])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    $false | (spl5_1 | ~spl5_5 | ~spl5_10 | ~spl5_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f310,f29])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (spl5_1 | ~spl5_5 | ~spl5_10 | ~spl5_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f304,f287])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    sK1 != k1_relat_1(sK4) | (spl5_1 | ~spl5_5 | ~spl5_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f286,f271])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    k2_relat_1(sK3) != k1_relat_1(sK4) | (spl5_1 | ~spl5_5 | ~spl5_10)),
% 0.21/0.50    inference(subsumption_resolution,[],[f285,f103])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_relat_1(sK4) | (spl5_1 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f284,f27])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (spl5_1 | ~spl5_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f283,f77])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f282,f24])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    k2_relat_1(sK3) != k1_relat_1(sK4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl5_1),
% 0.21/0.50    inference(subsumption_resolution,[],[f280,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ~v2_funct_1(sK3) | spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f52])).
% 0.21/0.50  fof(f295,plain,(
% 0.21/0.50    spl5_17),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f294])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    $false | spl5_17),
% 0.21/0.50    inference(subsumption_resolution,[],[f144,f29])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f142])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    spl5_10),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f261])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    $false | spl5_10),
% 0.21/0.50    inference(subsumption_resolution,[],[f256,f104])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ~v1_relat_1(sK4) | spl5_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    v1_relat_1(sK4)),
% 0.21/0.50    inference(resolution,[],[f29,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    spl5_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f161])).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    $false | spl5_5),
% 0.21/0.50    inference(subsumption_resolution,[],[f156,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f76])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    v1_relat_1(sK3)),
% 0.21/0.50    inference(resolution,[],[f26,f45])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ~spl5_3 | spl5_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f65,f61])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    k1_xboole_0 = sK1 | k1_xboole_0 != sK2),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ~spl5_1 | ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f56,f52])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ~v2_funct_1(sK4) | ~v2_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (17458)------------------------------
% 0.21/0.50  % (17458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17458)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (17458)Memory used [KB]: 6396
% 0.21/0.50  % (17458)Time elapsed: 0.066 s
% 0.21/0.50  % (17458)------------------------------
% 0.21/0.50  % (17458)------------------------------
% 0.21/0.50  % (17438)Success in time 0.139 s
%------------------------------------------------------------------------------
