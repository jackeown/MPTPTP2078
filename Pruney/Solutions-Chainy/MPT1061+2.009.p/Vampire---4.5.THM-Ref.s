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
% DateTime   : Thu Dec  3 13:07:33 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  161 (1762 expanded)
%              Number of leaves         :   26 ( 442 expanded)
%              Depth                    :   21
%              Number of atoms          :  458 (7181 expanded)
%              Number of equality atoms :   87 (1126 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1212,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f174,f230,f234,f439,f493,f502,f534,f781,f1210])).

fof(f1210,plain,
    ( ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f1201])).

fof(f1201,plain,
    ( $false
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f989,f844,f992,f88])).

fof(f88,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f992,plain,
    ( ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f966,f975])).

fof(f975,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f844,f955,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f955,plain,
    ( ~ v1_funct_2(k1_xboole_0,sK1,k1_xboole_0)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f741,f949])).

fof(f949,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK1)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f789,f767,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f767,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f744,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f744,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0))
    | ~ spl6_3
    | spl6_5
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f265,f735])).

fof(f735,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_3
    | spl6_5
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f173,f164,f719,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f719,plain,
    ( sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f264,f710])).

fof(f710,plain,
    ( sK1 = k1_relat_1(k7_relat_1(sK4,sK1))
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f49,f538])).

fof(f538,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | k1_relat_1(k7_relat_1(sK4,X1)) = X1 )
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f126,f492])).

fof(f492,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f490])).

fof(f490,plain,
    ( spl6_10
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f126,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_relat_1(sK4))
      | k1_relat_1(k7_relat_1(sK4,X1)) = X1 ) ),
    inference(resolution,[],[f103,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f103,plain,(
    v1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f48,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f48,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            | ~ v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
            | ~ v1_funct_1(k2_partfun1(X0,X3,X4,X1)) )
          & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
          & r1_tarski(X1,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
      & ~ v1_xboole_0(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ~ v1_xboole_0(X3)
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
           => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
                & r1_tarski(X1,X0) )
             => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
                & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ~ v1_xboole_0(X3)
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X4,X0,X3)
            & v1_funct_1(X4) )
         => ( ( r1_tarski(k7_relset_1(X0,X3,X4,X1),X2)
              & r1_tarski(X1,X0) )
           => ( m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2)
              & v1_funct_1(k2_partfun1(X0,X3,X4,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

fof(f49,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f264,plain,
    ( k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f164,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f164,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl6_3
  <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f173,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl6_5
  <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f265,plain,
    ( r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2))
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f164,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f789,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f787,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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

fof(f787,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f72,f785,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f785,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f739,f783])).

fof(f783,plain,
    ( k1_xboole_0 = k9_relat_1(sK4,sK1)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f434,f735])).

fof(f434,plain,
    ( sK2 = k9_relat_1(sK4,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl6_6
  <=> sK2 = k9_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f739,plain,
    ( m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_3
    | spl6_5
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f127,f735])).

fof(f127,plain,(
    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f108,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f108,plain,(
    r1_tarski(k9_relat_1(sK4,sK1),sK2) ),
    inference(backward_demodulation,[],[f50,f102])).

fof(f102,plain,(
    ! [X0] : k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0) ),
    inference(unit_resulting_resolution,[],[f48,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f50,plain,(
    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f741,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f173,f735])).

fof(f966,plain,
    ( ! [X0,X1] : sK1 = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f863,f954])).

fof(f954,plain,
    ( sK1 = k1_relat_1(k1_xboole_0)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f710,f949])).

fof(f863,plain,
    ( ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f361,f835])).

fof(f835,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0))
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f789,f538])).

fof(f361,plain,(
    ! [X0,X1] : k1_relat_1(k1_relat_1(k7_relat_1(sK4,k1_xboole_0))) = k1_relset_1(X0,X1,k1_relat_1(k7_relat_1(sK4,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f299,f76])).

fof(f299,plain,(
    ! [X0] : m1_subset_1(k1_relat_1(k7_relat_1(sK4,k1_xboole_0)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f278,f56])).

fof(f278,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,k1_xboole_0)),X0) ),
    inference(unit_resulting_resolution,[],[f275,f81])).

fof(f275,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK4,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f72,f211,f71])).

fof(f211,plain,(
    ! [X0] : m1_subset_1(k1_relat_1(k7_relat_1(sK4,X0)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f116,f56])).

fof(f116,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f103,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f844,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f299,f835])).

fof(f989,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f955,f975])).

fof(f781,plain,
    ( ~ spl6_3
    | spl6_5
    | spl6_7
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f772])).

fof(f772,plain,
    ( $false
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f86,f753])).

fof(f753,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f450,f735])).

fof(f450,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f449,f56])).

fof(f449,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f72,f440,f71])).

fof(f440,plain,
    ( r2_hidden(sK5(sK2,k9_relat_1(sK4,sK1)),sK2)
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f438,f81])).

fof(f438,plain,
    ( ~ r1_tarski(sK2,k9_relat_1(sK4,sK1))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl6_7
  <=> r1_tarski(sK2,k9_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f86,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f534,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f531])).

fof(f531,plain,
    ( $false
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f72,f505])).

fof(f505,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f51,f488])).

fof(f488,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f486])).

fof(f486,plain,
    ( spl6_9
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f51,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f502,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f496])).

fof(f496,plain,
    ( $false
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f105,f484,f56])).

fof(f484,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f482])).

fof(f482,plain,
    ( spl6_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f105,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK0,sK3)) ),
    inference(unit_resulting_resolution,[],[f48,f57])).

fof(f493,plain,
    ( ~ spl6_8
    | spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f107,f490,f486,f482])).

fof(f107,plain,
    ( sK0 = k1_relat_1(sK4)
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(backward_demodulation,[],[f97,f104])).

fof(f104,plain,(
    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4) ),
    inference(unit_resulting_resolution,[],[f48,f76])).

fof(f97,plain,
    ( k1_xboole_0 = sK3
    | sK0 = k1_relset_1(sK0,sK3,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) ),
    inference(resolution,[],[f47,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    v1_funct_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f439,plain,
    ( spl6_6
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f128,f436,f432])).

fof(f128,plain,
    ( ~ r1_tarski(sK2,k9_relat_1(sK4,sK1))
    | sK2 = k9_relat_1(sK4,sK1) ),
    inference(resolution,[],[f108,f60])).

fof(f234,plain,(
    spl6_4 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | spl6_4 ),
    inference(unit_resulting_resolution,[],[f113,f169])).

fof(f169,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl6_4
  <=> v1_funct_1(k7_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f113,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK4,X0)) ),
    inference(forward_demodulation,[],[f99,f101])).

fof(f101,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK0,sK3,sK4,X0) ),
    inference(unit_resulting_resolution,[],[f46,f48,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f46,f48,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f230,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f127,f217,f57])).

fof(f217,plain,
    ( ~ r1_tarski(k9_relat_1(sK4,sK1),sK2)
    | spl6_3 ),
    inference(forward_demodulation,[],[f208,f118])).

fof(f118,plain,(
    ! [X0] : k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f103,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f208,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2)
    | spl6_3 ),
    inference(unit_resulting_resolution,[],[f117,f165,f116,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f165,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f163])).

fof(f117,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK4,X0)) ),
    inference(unit_resulting_resolution,[],[f103,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f174,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f111,f171,f167,f163])).

fof(f111,plain,
    ( ~ v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)
    | ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(forward_demodulation,[],[f110,f101])).

fof(f110,plain,
    ( ~ v1_funct_1(k7_relat_1(sK4,sK1))
    | ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    inference(forward_demodulation,[],[f109,f101])).

fof(f109,plain,
    ( ~ m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) ),
    inference(backward_demodulation,[],[f45,f101])).

fof(f45,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1))
    | ~ v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)
    | ~ m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:05:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (19087)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (19094)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (19083)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (19086)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (19103)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (19085)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (19091)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (19095)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (19099)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.56  % (19084)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.57  % (19102)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.57  % (19107)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.57  % (19101)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.58  % (19093)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.58  % (19090)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.71/0.58  % (19082)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.71/0.58  % (19100)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.71/0.58  % (19109)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.71/0.59  % (19098)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.71/0.60  % (19089)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.71/0.60  % (19106)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.71/0.60  % (19108)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.71/0.60  % (19092)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.71/0.61  % (19088)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.71/0.61  % (19102)Refutation not found, incomplete strategy% (19102)------------------------------
% 1.71/0.61  % (19102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.61  % (19102)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.61  
% 1.71/0.61  % (19102)Memory used [KB]: 11129
% 1.71/0.61  % (19102)Time elapsed: 0.172 s
% 1.71/0.61  % (19102)------------------------------
% 1.71/0.61  % (19102)------------------------------
% 1.71/0.62  % (19080)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.71/0.62  % (19081)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.71/0.64  % (19105)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.71/0.64  % (19097)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.71/0.64  % (19104)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.71/0.64  % (19084)Refutation found. Thanks to Tanya!
% 1.71/0.64  % SZS status Theorem for theBenchmark
% 1.71/0.64  % SZS output start Proof for theBenchmark
% 1.71/0.64  fof(f1212,plain,(
% 1.71/0.64    $false),
% 1.71/0.64    inference(avatar_sat_refutation,[],[f174,f230,f234,f439,f493,f502,f534,f781,f1210])).
% 1.71/0.64  fof(f1210,plain,(
% 1.71/0.64    ~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10),
% 1.71/0.64    inference(avatar_contradiction_clause,[],[f1201])).
% 1.71/0.64  fof(f1201,plain,(
% 1.71/0.64    $false | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.64    inference(unit_resulting_resolution,[],[f989,f844,f992,f88])).
% 1.71/0.64  fof(f88,plain,(
% 1.71/0.64    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.71/0.64    inference(equality_resolution,[],[f67])).
% 1.71/0.64  fof(f67,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f36])).
% 1.71/0.64  fof(f36,plain,(
% 1.71/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.64    inference(flattening,[],[f35])).
% 1.71/0.64  fof(f35,plain,(
% 1.71/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.64    inference(ennf_transformation,[],[f19])).
% 1.71/0.64  fof(f19,axiom,(
% 1.71/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.71/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.71/0.64  fof(f992,plain,(
% 1.71/0.64    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.64    inference(backward_demodulation,[],[f966,f975])).
% 1.71/0.64  fof(f975,plain,(
% 1.71/0.64    k1_xboole_0 = sK1 | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.64    inference(unit_resulting_resolution,[],[f844,f955,f91])).
% 1.71/0.64  fof(f91,plain,(
% 1.71/0.64    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 1.71/0.64    inference(equality_resolution,[],[f90])).
% 1.71/0.64  fof(f90,plain,(
% 1.71/0.64    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.71/0.64    inference(equality_resolution,[],[f65])).
% 1.71/0.64  fof(f65,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f36])).
% 1.71/0.64  fof(f955,plain,(
% 1.71/0.64    ~v1_funct_2(k1_xboole_0,sK1,k1_xboole_0) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.64    inference(backward_demodulation,[],[f741,f949])).
% 1.71/0.64  fof(f949,plain,(
% 1.71/0.64    k1_xboole_0 = k7_relat_1(sK4,sK1) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.64    inference(unit_resulting_resolution,[],[f789,f767,f60])).
% 1.71/0.64  fof(f60,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.71/0.64    inference(cnf_transformation,[],[f3])).
% 1.71/0.64  fof(f3,axiom,(
% 1.71/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.71/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.71/0.64  fof(f767,plain,(
% 1.71/0.64    r1_tarski(k7_relat_1(sK4,sK1),k1_xboole_0) | (~spl6_3 | spl6_5 | ~spl6_10)),
% 1.71/0.64    inference(forward_demodulation,[],[f744,f92])).
% 1.71/0.64  fof(f92,plain,(
% 1.71/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.71/0.64    inference(equality_resolution,[],[f79])).
% 1.71/0.64  fof(f79,plain,(
% 1.71/0.64    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f4])).
% 1.71/0.64  fof(f4,axiom,(
% 1.71/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.71/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.71/0.64  fof(f744,plain,(
% 1.71/0.64    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,k1_xboole_0)) | (~spl6_3 | spl6_5 | ~spl6_10)),
% 1.71/0.64    inference(backward_demodulation,[],[f265,f735])).
% 1.71/0.64  fof(f735,plain,(
% 1.71/0.64    k1_xboole_0 = sK2 | (~spl6_3 | spl6_5 | ~spl6_10)),
% 1.71/0.64    inference(unit_resulting_resolution,[],[f173,f164,f719,f69])).
% 1.71/0.64  fof(f69,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f36])).
% 1.71/0.64  fof(f719,plain,(
% 1.71/0.64    sK1 = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | (~spl6_3 | ~spl6_10)),
% 1.71/0.64    inference(backward_demodulation,[],[f264,f710])).
% 1.71/0.64  fof(f710,plain,(
% 1.71/0.64    sK1 = k1_relat_1(k7_relat_1(sK4,sK1)) | ~spl6_10),
% 1.71/0.64    inference(unit_resulting_resolution,[],[f49,f538])).
% 1.71/0.64  fof(f538,plain,(
% 1.71/0.64    ( ! [X1] : (~r1_tarski(X1,sK0) | k1_relat_1(k7_relat_1(sK4,X1)) = X1) ) | ~spl6_10),
% 1.71/0.64    inference(backward_demodulation,[],[f126,f492])).
% 1.71/0.64  fof(f492,plain,(
% 1.71/0.64    sK0 = k1_relat_1(sK4) | ~spl6_10),
% 1.71/0.64    inference(avatar_component_clause,[],[f490])).
% 1.71/0.64  fof(f490,plain,(
% 1.71/0.64    spl6_10 <=> sK0 = k1_relat_1(sK4)),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.71/0.64  fof(f126,plain,(
% 1.71/0.64    ( ! [X1] : (~r1_tarski(X1,k1_relat_1(sK4)) | k1_relat_1(k7_relat_1(sK4,X1)) = X1) )),
% 1.71/0.64    inference(resolution,[],[f103,f61])).
% 1.71/0.64  fof(f61,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.71/0.64    inference(cnf_transformation,[],[f32])).
% 1.71/0.64  fof(f32,plain,(
% 1.71/0.64    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.71/0.64    inference(flattening,[],[f31])).
% 1.71/0.64  fof(f31,plain,(
% 1.71/0.64    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.71/0.64    inference(ennf_transformation,[],[f13])).
% 1.71/0.64  fof(f13,axiom,(
% 1.71/0.64    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.71/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).
% 1.71/0.64  fof(f103,plain,(
% 1.71/0.64    v1_relat_1(sK4)),
% 1.71/0.64    inference(unit_resulting_resolution,[],[f48,f63])).
% 1.71/0.64  fof(f63,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.64    inference(cnf_transformation,[],[f34])).
% 1.71/0.64  fof(f34,plain,(
% 1.71/0.64    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.64    inference(ennf_transformation,[],[f14])).
% 1.71/0.64  fof(f14,axiom,(
% 1.71/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.71/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.71/0.64  fof(f48,plain,(
% 1.71/0.64    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.71/0.64    inference(cnf_transformation,[],[f25])).
% 1.71/0.64  fof(f25,plain,(
% 1.71/0.64    ? [X0,X1,X2,X3] : (? [X4] : ((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & ~v1_xboole_0(X3))),
% 1.71/0.64    inference(flattening,[],[f24])).
% 1.71/0.64  fof(f24,plain,(
% 1.71/0.64    ? [X0,X1,X2,X3] : (? [X4] : (((~m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) | ~v1_funct_1(k2_partfun1(X0,X3,X4,X1))) & (r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4))) & ~v1_xboole_0(X3))),
% 1.71/0.64    inference(ennf_transformation,[],[f23])).
% 1.71/0.64  fof(f23,negated_conjecture,(
% 1.71/0.64    ~! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.71/0.64    inference(negated_conjecture,[],[f22])).
% 1.71/0.64  fof(f22,conjecture,(
% 1.71/0.64    ! [X0,X1,X2,X3] : (~v1_xboole_0(X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => ((r1_tarski(k7_relset_1(X0,X3,X4,X1),X2) & r1_tarski(X1,X0)) => (m1_subset_1(k2_partfun1(X0,X3,X4,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(k2_partfun1(X0,X3,X4,X1),X1,X2) & v1_funct_1(k2_partfun1(X0,X3,X4,X1))))))),
% 1.71/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).
% 1.71/0.64  fof(f49,plain,(
% 1.71/0.64    r1_tarski(sK1,sK0)),
% 1.71/0.64    inference(cnf_transformation,[],[f25])).
% 1.71/0.64  fof(f264,plain,(
% 1.71/0.64    k1_relat_1(k7_relat_1(sK4,sK1)) = k1_relset_1(sK1,sK2,k7_relat_1(sK4,sK1)) | ~spl6_3),
% 1.71/0.64    inference(unit_resulting_resolution,[],[f164,f76])).
% 1.71/0.64  fof(f76,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f42])).
% 1.71/0.64  fof(f42,plain,(
% 1.71/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.64    inference(ennf_transformation,[],[f16])).
% 1.71/0.65  fof(f16,axiom,(
% 1.71/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.71/0.65  fof(f164,plain,(
% 1.71/0.65    m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_3),
% 1.71/0.65    inference(avatar_component_clause,[],[f163])).
% 1.71/0.65  fof(f163,plain,(
% 1.71/0.65    spl6_3 <=> m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.71/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.71/0.65  fof(f173,plain,(
% 1.71/0.65    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | spl6_5),
% 1.71/0.65    inference(avatar_component_clause,[],[f171])).
% 1.71/0.65  fof(f171,plain,(
% 1.71/0.65    spl6_5 <=> v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2)),
% 1.71/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.71/0.65  fof(f265,plain,(
% 1.71/0.65    r1_tarski(k7_relat_1(sK4,sK1),k2_zfmisc_1(sK1,sK2)) | ~spl6_3),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f164,f57])).
% 1.71/0.65  fof(f57,plain,(
% 1.71/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.71/0.65    inference(cnf_transformation,[],[f5])).
% 1.71/0.65  fof(f5,axiom,(
% 1.71/0.65    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.71/0.65  fof(f789,plain,(
% 1.71/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f787,f81])).
% 1.71/0.65  fof(f81,plain,(
% 1.71/0.65    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.71/0.65    inference(cnf_transformation,[],[f43])).
% 1.71/0.65  fof(f43,plain,(
% 1.71/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.71/0.65    inference(ennf_transformation,[],[f1])).
% 1.71/0.65  fof(f1,axiom,(
% 1.71/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.71/0.65  fof(f787,plain,(
% 1.71/0.65    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f72,f785,f71])).
% 1.71/0.65  fof(f71,plain,(
% 1.71/0.65    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.71/0.65    inference(cnf_transformation,[],[f37])).
% 1.71/0.65  fof(f37,plain,(
% 1.71/0.65    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.71/0.65    inference(ennf_transformation,[],[f6])).
% 1.71/0.65  fof(f6,axiom,(
% 1.71/0.65    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.71/0.65  fof(f785,plain,(
% 1.71/0.65    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.65    inference(backward_demodulation,[],[f739,f783])).
% 1.71/0.65  fof(f783,plain,(
% 1.71/0.65    k1_xboole_0 = k9_relat_1(sK4,sK1) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.65    inference(forward_demodulation,[],[f434,f735])).
% 1.71/0.65  fof(f434,plain,(
% 1.71/0.65    sK2 = k9_relat_1(sK4,sK1) | ~spl6_6),
% 1.71/0.65    inference(avatar_component_clause,[],[f432])).
% 1.71/0.65  fof(f432,plain,(
% 1.71/0.65    spl6_6 <=> sK2 = k9_relat_1(sK4,sK1)),
% 1.71/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.71/0.65  fof(f739,plain,(
% 1.71/0.65    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl6_3 | spl6_5 | ~spl6_10)),
% 1.71/0.65    inference(backward_demodulation,[],[f127,f735])).
% 1.71/0.65  fof(f127,plain,(
% 1.71/0.65    m1_subset_1(k9_relat_1(sK4,sK1),k1_zfmisc_1(sK2))),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f108,f56])).
% 1.71/0.65  fof(f56,plain,(
% 1.71/0.65    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.71/0.65    inference(cnf_transformation,[],[f5])).
% 1.71/0.65  fof(f108,plain,(
% 1.71/0.65    r1_tarski(k9_relat_1(sK4,sK1),sK2)),
% 1.71/0.65    inference(backward_demodulation,[],[f50,f102])).
% 1.71/0.65  fof(f102,plain,(
% 1.71/0.65    ( ! [X0] : (k7_relset_1(sK0,sK3,sK4,X0) = k9_relat_1(sK4,X0)) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f48,f55])).
% 1.71/0.65  fof(f55,plain,(
% 1.71/0.65    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.65    inference(cnf_transformation,[],[f30])).
% 1.71/0.65  fof(f30,plain,(
% 1.71/0.65    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.65    inference(ennf_transformation,[],[f17])).
% 1.71/0.65  fof(f17,axiom,(
% 1.71/0.65    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.71/0.65  fof(f50,plain,(
% 1.71/0.65    r1_tarski(k7_relset_1(sK0,sK3,sK4,sK1),sK2)),
% 1.71/0.65    inference(cnf_transformation,[],[f25])).
% 1.71/0.65  fof(f72,plain,(
% 1.71/0.65    v1_xboole_0(k1_xboole_0)),
% 1.71/0.65    inference(cnf_transformation,[],[f2])).
% 1.71/0.65  fof(f2,axiom,(
% 1.71/0.65    v1_xboole_0(k1_xboole_0)),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.71/0.65  fof(f741,plain,(
% 1.71/0.65    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,k1_xboole_0) | (~spl6_3 | spl6_5 | ~spl6_10)),
% 1.71/0.65    inference(backward_demodulation,[],[f173,f735])).
% 1.71/0.65  fof(f966,plain,(
% 1.71/0.65    ( ! [X0,X1] : (sK1 = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.65    inference(backward_demodulation,[],[f863,f954])).
% 1.71/0.65  fof(f954,plain,(
% 1.71/0.65    sK1 = k1_relat_1(k1_xboole_0) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.65    inference(backward_demodulation,[],[f710,f949])).
% 1.71/0.65  fof(f863,plain,(
% 1.71/0.65    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) ) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.65    inference(backward_demodulation,[],[f361,f835])).
% 1.71/0.65  fof(f835,plain,(
% 1.71/0.65    k1_xboole_0 = k1_relat_1(k7_relat_1(sK4,k1_xboole_0)) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f789,f538])).
% 1.71/0.65  fof(f361,plain,(
% 1.71/0.65    ( ! [X0,X1] : (k1_relat_1(k1_relat_1(k7_relat_1(sK4,k1_xboole_0))) = k1_relset_1(X0,X1,k1_relat_1(k7_relat_1(sK4,k1_xboole_0)))) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f299,f76])).
% 1.71/0.65  fof(f299,plain,(
% 1.71/0.65    ( ! [X0] : (m1_subset_1(k1_relat_1(k7_relat_1(sK4,k1_xboole_0)),k1_zfmisc_1(X0))) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f278,f56])).
% 1.71/0.65  fof(f278,plain,(
% 1.71/0.65    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,k1_xboole_0)),X0)) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f275,f81])).
% 1.71/0.65  fof(f275,plain,(
% 1.71/0.65    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK4,k1_xboole_0)))) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f72,f211,f71])).
% 1.71/0.65  fof(f211,plain,(
% 1.71/0.65    ( ! [X0] : (m1_subset_1(k1_relat_1(k7_relat_1(sK4,X0)),k1_zfmisc_1(X0))) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f116,f56])).
% 1.71/0.65  fof(f116,plain,(
% 1.71/0.65    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK4,X0)),X0)) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f103,f62])).
% 1.71/0.65  fof(f62,plain,(
% 1.71/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)) )),
% 1.71/0.65    inference(cnf_transformation,[],[f33])).
% 1.71/0.65  fof(f33,plain,(
% 1.71/0.65    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.71/0.65    inference(ennf_transformation,[],[f12])).
% 1.71/0.65  fof(f12,axiom,(
% 1.71/0.65    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 1.71/0.65  fof(f844,plain,(
% 1.71/0.65    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.65    inference(backward_demodulation,[],[f299,f835])).
% 1.71/0.65  fof(f989,plain,(
% 1.71/0.65    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_3 | spl6_5 | ~spl6_6 | ~spl6_10)),
% 1.71/0.65    inference(backward_demodulation,[],[f955,f975])).
% 1.71/0.65  fof(f781,plain,(
% 1.71/0.65    ~spl6_3 | spl6_5 | spl6_7 | ~spl6_10),
% 1.71/0.65    inference(avatar_contradiction_clause,[],[f772])).
% 1.71/0.65  fof(f772,plain,(
% 1.71/0.65    $false | (~spl6_3 | spl6_5 | spl6_7 | ~spl6_10)),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f86,f753])).
% 1.71/0.65  fof(f753,plain,(
% 1.71/0.65    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl6_3 | spl6_5 | spl6_7 | ~spl6_10)),
% 1.71/0.65    inference(backward_demodulation,[],[f450,f735])).
% 1.71/0.65  fof(f450,plain,(
% 1.71/0.65    ~r1_tarski(sK2,k1_xboole_0) | spl6_7),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f449,f56])).
% 1.71/0.65  fof(f449,plain,(
% 1.71/0.65    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl6_7),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f72,f440,f71])).
% 1.71/0.65  fof(f440,plain,(
% 1.71/0.65    r2_hidden(sK5(sK2,k9_relat_1(sK4,sK1)),sK2) | spl6_7),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f438,f81])).
% 1.71/0.65  fof(f438,plain,(
% 1.71/0.65    ~r1_tarski(sK2,k9_relat_1(sK4,sK1)) | spl6_7),
% 1.71/0.65    inference(avatar_component_clause,[],[f436])).
% 1.71/0.65  fof(f436,plain,(
% 1.71/0.65    spl6_7 <=> r1_tarski(sK2,k9_relat_1(sK4,sK1))),
% 1.71/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.71/0.65  fof(f86,plain,(
% 1.71/0.65    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.71/0.65    inference(equality_resolution,[],[f58])).
% 1.71/0.65  fof(f58,plain,(
% 1.71/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.71/0.65    inference(cnf_transformation,[],[f3])).
% 1.71/0.65  fof(f534,plain,(
% 1.71/0.65    ~spl6_9),
% 1.71/0.65    inference(avatar_contradiction_clause,[],[f531])).
% 1.71/0.65  fof(f531,plain,(
% 1.71/0.65    $false | ~spl6_9),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f72,f505])).
% 1.71/0.65  fof(f505,plain,(
% 1.71/0.65    ~v1_xboole_0(k1_xboole_0) | ~spl6_9),
% 1.71/0.65    inference(backward_demodulation,[],[f51,f488])).
% 1.71/0.65  fof(f488,plain,(
% 1.71/0.65    k1_xboole_0 = sK3 | ~spl6_9),
% 1.71/0.65    inference(avatar_component_clause,[],[f486])).
% 1.71/0.65  fof(f486,plain,(
% 1.71/0.65    spl6_9 <=> k1_xboole_0 = sK3),
% 1.71/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.71/0.65  fof(f51,plain,(
% 1.71/0.65    ~v1_xboole_0(sK3)),
% 1.71/0.65    inference(cnf_transformation,[],[f25])).
% 1.71/0.65  fof(f502,plain,(
% 1.71/0.65    spl6_8),
% 1.71/0.65    inference(avatar_contradiction_clause,[],[f496])).
% 1.71/0.65  fof(f496,plain,(
% 1.71/0.65    $false | spl6_8),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f105,f484,f56])).
% 1.71/0.65  fof(f484,plain,(
% 1.71/0.65    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3))) | spl6_8),
% 1.71/0.65    inference(avatar_component_clause,[],[f482])).
% 1.71/0.65  fof(f482,plain,(
% 1.71/0.65    spl6_8 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.71/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.71/0.65  fof(f105,plain,(
% 1.71/0.65    r1_tarski(sK4,k2_zfmisc_1(sK0,sK3))),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f48,f57])).
% 1.71/0.65  fof(f493,plain,(
% 1.71/0.65    ~spl6_8 | spl6_9 | spl6_10),
% 1.71/0.65    inference(avatar_split_clause,[],[f107,f490,f486,f482])).
% 1.71/0.65  fof(f107,plain,(
% 1.71/0.65    sK0 = k1_relat_1(sK4) | k1_xboole_0 = sK3 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.71/0.65    inference(backward_demodulation,[],[f97,f104])).
% 1.71/0.65  fof(f104,plain,(
% 1.71/0.65    k1_relset_1(sK0,sK3,sK4) = k1_relat_1(sK4)),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f48,f76])).
% 1.71/0.65  fof(f97,plain,(
% 1.71/0.65    k1_xboole_0 = sK3 | sK0 = k1_relset_1(sK0,sK3,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK3)))),
% 1.71/0.65    inference(resolution,[],[f47,f70])).
% 1.71/0.65  fof(f70,plain,(
% 1.71/0.65    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.71/0.65    inference(cnf_transformation,[],[f36])).
% 1.71/0.65  fof(f47,plain,(
% 1.71/0.65    v1_funct_2(sK4,sK0,sK3)),
% 1.71/0.65    inference(cnf_transformation,[],[f25])).
% 1.71/0.65  fof(f439,plain,(
% 1.71/0.65    spl6_6 | ~spl6_7),
% 1.71/0.65    inference(avatar_split_clause,[],[f128,f436,f432])).
% 1.71/0.65  fof(f128,plain,(
% 1.71/0.65    ~r1_tarski(sK2,k9_relat_1(sK4,sK1)) | sK2 = k9_relat_1(sK4,sK1)),
% 1.71/0.65    inference(resolution,[],[f108,f60])).
% 1.71/0.65  fof(f234,plain,(
% 1.71/0.65    spl6_4),
% 1.71/0.65    inference(avatar_contradiction_clause,[],[f231])).
% 1.71/0.65  fof(f231,plain,(
% 1.71/0.65    $false | spl6_4),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f113,f169])).
% 1.71/0.65  fof(f169,plain,(
% 1.71/0.65    ~v1_funct_1(k7_relat_1(sK4,sK1)) | spl6_4),
% 1.71/0.65    inference(avatar_component_clause,[],[f167])).
% 1.71/0.65  fof(f167,plain,(
% 1.71/0.65    spl6_4 <=> v1_funct_1(k7_relat_1(sK4,sK1))),
% 1.71/0.65    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.71/0.65  fof(f113,plain,(
% 1.71/0.65    ( ! [X0] : (v1_funct_1(k7_relat_1(sK4,X0))) )),
% 1.71/0.65    inference(forward_demodulation,[],[f99,f101])).
% 1.71/0.65  fof(f101,plain,(
% 1.71/0.65    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK0,sK3,sK4,X0)) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f46,f48,f54])).
% 1.71/0.65  fof(f54,plain,(
% 1.71/0.65    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 1.71/0.65    inference(cnf_transformation,[],[f29])).
% 1.71/0.65  fof(f29,plain,(
% 1.71/0.65    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.71/0.65    inference(flattening,[],[f28])).
% 1.71/0.65  fof(f28,plain,(
% 1.71/0.65    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.71/0.65    inference(ennf_transformation,[],[f21])).
% 1.71/0.65  fof(f21,axiom,(
% 1.71/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.71/0.65  fof(f46,plain,(
% 1.71/0.65    v1_funct_1(sK4)),
% 1.71/0.65    inference(cnf_transformation,[],[f25])).
% 1.71/0.65  fof(f99,plain,(
% 1.71/0.65    ( ! [X0] : (v1_funct_1(k2_partfun1(sK0,sK3,sK4,X0))) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f46,f48,f52])).
% 1.71/0.65  fof(f52,plain,(
% 1.71/0.65    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.71/0.65    inference(cnf_transformation,[],[f27])).
% 1.71/0.65  fof(f27,plain,(
% 1.71/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.71/0.65    inference(flattening,[],[f26])).
% 1.71/0.65  fof(f26,plain,(
% 1.71/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.71/0.65    inference(ennf_transformation,[],[f20])).
% 1.71/0.65  fof(f20,axiom,(
% 1.71/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 1.71/0.65  fof(f230,plain,(
% 1.71/0.65    spl6_3),
% 1.71/0.65    inference(avatar_contradiction_clause,[],[f225])).
% 1.71/0.65  fof(f225,plain,(
% 1.71/0.65    $false | spl6_3),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f127,f217,f57])).
% 1.71/0.65  fof(f217,plain,(
% 1.71/0.65    ~r1_tarski(k9_relat_1(sK4,sK1),sK2) | spl6_3),
% 1.71/0.65    inference(forward_demodulation,[],[f208,f118])).
% 1.71/0.65  fof(f118,plain,(
% 1.71/0.65    ( ! [X0] : (k9_relat_1(sK4,X0) = k2_relat_1(k7_relat_1(sK4,X0))) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f103,f74])).
% 1.71/0.65  fof(f74,plain,(
% 1.71/0.65    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.71/0.65    inference(cnf_transformation,[],[f39])).
% 1.71/0.65  fof(f39,plain,(
% 1.71/0.65    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.71/0.65    inference(ennf_transformation,[],[f11])).
% 1.71/0.65  fof(f11,axiom,(
% 1.71/0.65    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.71/0.65  fof(f208,plain,(
% 1.71/0.65    ~r1_tarski(k2_relat_1(k7_relat_1(sK4,sK1)),sK2) | spl6_3),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f117,f165,f116,f75])).
% 1.71/0.65  fof(f75,plain,(
% 1.71/0.65    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 1.71/0.65    inference(cnf_transformation,[],[f41])).
% 1.71/0.65  fof(f41,plain,(
% 1.71/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 1.71/0.65    inference(flattening,[],[f40])).
% 1.71/0.65  fof(f40,plain,(
% 1.71/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 1.71/0.65    inference(ennf_transformation,[],[f18])).
% 1.71/0.65  fof(f18,axiom,(
% 1.71/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 1.71/0.65  fof(f165,plain,(
% 1.71/0.65    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl6_3),
% 1.71/0.65    inference(avatar_component_clause,[],[f163])).
% 1.71/0.65  fof(f117,plain,(
% 1.71/0.65    ( ! [X0] : (v1_relat_1(k7_relat_1(sK4,X0))) )),
% 1.71/0.65    inference(unit_resulting_resolution,[],[f103,f73])).
% 1.71/0.65  fof(f73,plain,(
% 1.71/0.65    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.71/0.65    inference(cnf_transformation,[],[f38])).
% 1.71/0.65  fof(f38,plain,(
% 1.71/0.65    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.71/0.65    inference(ennf_transformation,[],[f9])).
% 1.71/0.65  fof(f9,axiom,(
% 1.71/0.65    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.71/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.71/0.65  fof(f174,plain,(
% 1.71/0.65    ~spl6_3 | ~spl6_4 | ~spl6_5),
% 1.71/0.65    inference(avatar_split_clause,[],[f111,f171,f167,f163])).
% 1.71/0.65  fof(f111,plain,(
% 1.71/0.65    ~v1_funct_2(k7_relat_1(sK4,sK1),sK1,sK2) | ~v1_funct_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.71/0.65    inference(forward_demodulation,[],[f110,f101])).
% 1.71/0.65  fof(f110,plain,(
% 1.71/0.65    ~v1_funct_1(k7_relat_1(sK4,sK1)) | ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.71/0.65    inference(forward_demodulation,[],[f109,f101])).
% 1.71/0.65  fof(f109,plain,(
% 1.71/0.65    ~m1_subset_1(k7_relat_1(sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2)),
% 1.71/0.65    inference(backward_demodulation,[],[f45,f101])).
% 1.71/0.65  fof(f45,plain,(
% 1.71/0.65    ~v1_funct_1(k2_partfun1(sK0,sK3,sK4,sK1)) | ~v1_funct_2(k2_partfun1(sK0,sK3,sK4,sK1),sK1,sK2) | ~m1_subset_1(k2_partfun1(sK0,sK3,sK4,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.71/0.65    inference(cnf_transformation,[],[f25])).
% 1.71/0.65  % SZS output end Proof for theBenchmark
% 1.71/0.65  % (19084)------------------------------
% 1.71/0.65  % (19084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.65  % (19084)Termination reason: Refutation
% 1.71/0.65  
% 1.71/0.65  % (19084)Memory used [KB]: 6908
% 1.71/0.65  % (19084)Time elapsed: 0.224 s
% 1.71/0.65  % (19084)------------------------------
% 1.71/0.65  % (19084)------------------------------
% 1.71/0.65  % (19079)Success in time 0.283 s
%------------------------------------------------------------------------------
