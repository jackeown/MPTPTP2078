%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t189_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:39 EDT 2019

% Result     : Theorem 0.71s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 141 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   21
%              Number of atoms          :  233 ( 637 expanded)
%              Number of equality atoms :   52 (  54 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f146,f204])).

fof(f204,plain,(
    ~ spl9_0 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl9_0 ),
    inference(subsumption_resolution,[],[f202,f60])).

fof(f60,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X3,X0,X1)
                      & v1_funct_1(X3) )
                   => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t189_funct_2.p',t189_funct_2)).

fof(f202,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ spl9_0 ),
    inference(subsumption_resolution,[],[f201,f62])).

fof(f62,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f201,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ spl9_0 ),
    inference(resolution,[],[f199,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t189_funct_2.p',t2_subset)).

fof(f199,plain,
    ( ~ r2_hidden(sK2,sK0)
    | ~ spl9_0 ),
    inference(forward_demodulation,[],[f198,f156])).

fof(f156,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ spl9_0 ),
    inference(subsumption_resolution,[],[f153,f58])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f153,plain,
    ( k1_relat_1(sK3) = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_0 ),
    inference(superposition,[],[f117,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t189_funct_2.p',redefinition_k1_relset_1)).

fof(f117,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_0
  <=> k1_relset_1(sK0,sK1,sK3) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f198,plain,(
    ~ r2_hidden(sK2,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f197,f107])).

fof(f107,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f58,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t189_funct_2.p',cc1_relset_1)).

fof(f197,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f195,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f195,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r2_hidden(sK2,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f194,f97])).

fof(f97,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t189_funct_2.p',d5_funct_1)).

fof(f194,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f192,f58])).

fof(f192,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f187,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t189_funct_2.p',redefinition_k2_relset_1)).

fof(f187,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f186,f62])).

fof(f186,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f185,f60])).

fof(f185,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f184,f58])).

fof(f184,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f183,f57])).

fof(f57,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f183,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f168,f56])).

fof(f168,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK2),k2_relset_1(sK0,sK1,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f59,f93])).

fof(f93,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t189_funct_2.p',redefinition_k3_funct_2)).

fof(f59,plain,(
    ~ r2_hidden(k3_funct_2(sK0,sK1,sK3,sK2),k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f146,plain,(
    ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl9_2 ),
    inference(resolution,[],[f144,f63])).

fof(f63,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t189_funct_2.p',dt_o_0_0_xboole_0)).

fof(f144,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl9_2 ),
    inference(duplicate_literal_removal,[],[f143])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl9_2 ),
    inference(superposition,[],[f138,f64])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t189_funct_2.p',t6_boole)).

fof(f138,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl9_2 ),
    inference(backward_demodulation,[],[f123,f61])).

fof(f61,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f123,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl9_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f124,plain,
    ( spl9_0
    | spl9_2 ),
    inference(avatar_split_clause,[],[f111,f122,f116])).

fof(f111,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(subsumption_resolution,[],[f106,f57])).

fof(f106,plain,
    ( k1_xboole_0 = sK1
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | ~ v1_funct_2(sK3,sK0,sK1) ),
    inference(resolution,[],[f58,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t189_funct_2.p',d1_funct_2)).
%------------------------------------------------------------------------------
