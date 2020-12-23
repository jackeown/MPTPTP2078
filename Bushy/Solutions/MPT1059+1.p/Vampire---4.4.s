%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t176_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:37 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 140 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   21
%              Number of atoms          :  229 ( 633 expanded)
%              Number of equality atoms :   56 ( 114 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f141,f173])).

fof(f173,plain,(
    ~ spl6_0 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | ~ spl6_0 ),
    inference(subsumption_resolution,[],[f171,f56])).

fof(f56,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k7_partfun1(X1,X2,X3) != k3_funct_2(X0,X1,X2,X3)
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k7_partfun1(X1,X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t176_funct_2.p',t176_funct_2)).

fof(f171,plain,
    ( ~ m1_subset_1(sK3,sK0)
    | ~ spl6_0 ),
    inference(subsumption_resolution,[],[f170,f62])).

fof(f62,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f170,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK3,sK0)
    | ~ spl6_0 ),
    inference(resolution,[],[f169,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t176_funct_2.p',t2_subset)).

fof(f169,plain,
    ( ~ r2_hidden(sK3,sK0)
    | ~ spl6_0 ),
    inference(forward_demodulation,[],[f168,f153])).

fof(f153,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl6_0 ),
    inference(subsumption_resolution,[],[f150,f60])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f150,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_0 ),
    inference(superposition,[],[f111,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t176_funct_2.p',redefinition_k1_relset_1)).

fof(f111,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_0
  <=> k1_relset_1(sK0,sK1,sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f168,plain,(
    ~ r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f167,f101])).

fof(f101,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f60,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t176_funct_2.p',cc1_relset_1)).

fof(f167,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f166,f58])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f166,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f165,f100])).

fof(f100,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f60,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t176_funct_2.p',cc2_relset_1)).

fof(f165,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k1_funct_1(sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f160,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t176_funct_2.p',d8_partfun1)).

fof(f160,plain,(
    k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f159,f62])).

fof(f159,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f158,f56])).

fof(f158,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f157,f60])).

fof(f157,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f156,f59])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f156,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f155,f58])).

fof(f155,plain,
    ( k7_partfun1(sK1,sK2,sK3) != k1_funct_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f57,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t176_funct_2.p',redefinition_k3_funct_2)).

fof(f57,plain,(
    k7_partfun1(sK1,sK2,sK3) != k3_funct_2(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f141,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl6_2 ),
    inference(resolution,[],[f139,f63])).

fof(f63,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t176_funct_2.p',dt_o_0_0_xboole_0)).

fof(f139,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl6_2 ),
    inference(superposition,[],[f132,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t176_funct_2.p',t6_boole)).

fof(f132,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f117,f61])).

fof(f61,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f117,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f118,plain,
    ( spl6_0
    | spl6_2 ),
    inference(avatar_split_clause,[],[f105,f116,f110])).

fof(f105,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(subsumption_resolution,[],[f98,f59])).

fof(f98,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f60,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t176_funct_2.p',d1_funct_2)).
%------------------------------------------------------------------------------
