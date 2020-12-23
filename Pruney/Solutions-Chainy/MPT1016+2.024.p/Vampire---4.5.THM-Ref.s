%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 (4808 expanded)
%              Number of leaves         :   12 ( 979 expanded)
%              Depth                    :   34
%              Number of atoms          :  311 (22155 expanded)
%              Number of equality atoms :   92 (5064 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f355,plain,(
    $false ),
    inference(subsumption_resolution,[],[f354,f139])).

fof(f139,plain,(
    sK2 != sK3 ),
    inference(resolution,[],[f135,f32])).

fof(f32,plain,
    ( ~ v2_funct_1(sK1)
    | sK2 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f135,plain,(
    v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f134,f92])).

fof(f92,plain,
    ( sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f64,f73])).

fof(f73,plain,(
    v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f70,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f70,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(resolution,[],[f36,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,
    ( ~ v1_relat_1(sK1)
    | sK4(sK1) != sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f34,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sK4(X0) != sK5(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f134,plain,
    ( v2_funct_1(sK1)
    | sK4(sK1) = sK5(sK1) ),
    inference(subsumption_resolution,[],[f132,f93])).

fof(f93,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) ),
    inference(resolution,[],[f63,f73])).

fof(f63,plain,
    ( ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f34,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f132,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,
    ( v2_funct_1(sK1)
    | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1))
    | sK4(sK1) = sK5(sK1)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f104,f106])).

fof(f106,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f89,f72])).

fof(f72,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f68,f69])).

fof(f69,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(resolution,[],[f36,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f68,plain,(
    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f36,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f89,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))
      | v2_funct_1(sK1)
      | r2_hidden(sK5(sK1),X1) ) ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f86,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f62,f73])).

fof(f62,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f34,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v2_funct_1(sK1)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK4(sK1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( v2_funct_1(sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1))
      | sK4(sK1) = X0
      | v2_funct_1(sK1) ) ),
    inference(resolution,[],[f98,f33])).

fof(f33,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f83,f72])).

fof(f83,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1))
      | v2_funct_1(sK1)
      | r2_hidden(sK4(sK1),X1) ) ),
    inference(resolution,[],[f80,f46])).

fof(f80,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f61,f73])).

fof(f61,plain,
    ( ~ v1_relat_1(sK1)
    | r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f34,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0),k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f354,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f349,f138])).

fof(f138,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(resolution,[],[f135,f31])).

fof(f31,plain,
    ( ~ v2_funct_1(sK1)
    | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f349,plain,
    ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f330,f231])).

fof(f231,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f187,f135])).

fof(f187,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ v2_funct_1(sK1) ),
    inference(backward_demodulation,[],[f30,f185])).

fof(f185,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f184,f139])).

fof(f184,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,
    ( sK2 = sK3
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f172,f170])).

fof(f170,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f169,f138])).

fof(f169,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f168,f135])).

fof(f168,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f155,f67])).

fof(f67,plain,
    ( ~ sP6(sK1,sK0)
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f66,f36])).

fof(f66,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(subsumption_resolution,[],[f65,f34])).

fof(f65,plain,
    ( ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v2_funct_1(sK1)
    | k1_xboole_0 = sK0
    | ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f35,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | k1_xboole_0 = X1
      | ~ sP6(X3,X0) ) ),
    inference(general_splitting,[],[f49,f59_D])).

fof(f59,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | sP6(X3,X0) ) ),
    inference(cnf_transformation,[],[f59_D])).

fof(f59_D,plain,(
    ! [X0,X3] :
      ( ! [X2] :
          ( ~ r2_hidden(X2,X0)
          | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 )
    <=> ~ sP6(X3,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f35,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f155,plain,(
    ! [X3] :
      ( sP6(X3,sK0)
      | sK3 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK3)) ) ),
    inference(resolution,[],[f140,f59])).

fof(f140,plain,(
    r2_hidden(sK3,sK0) ),
    inference(resolution,[],[f135,f30])).

fof(f172,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f171,f135])).

fof(f171,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK1) ),
    inference(resolution,[],[f167,f67])).

fof(f167,plain,(
    ! [X3] :
      ( sP6(X3,sK0)
      | sK2 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK2)) ) ),
    inference(resolution,[],[f141,f59])).

fof(f141,plain,(
    r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f135,f29])).

fof(f29,plain,
    ( ~ v2_funct_1(sK1)
    | r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,
    ( ~ v2_funct_1(sK1)
    | r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f330,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0)
      | sK2 = X0 ) ),
    inference(resolution,[],[f294,f230])).

fof(f230,plain,(
    r2_hidden(sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f186,f135])).

fof(f186,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ v2_funct_1(sK1) ),
    inference(backward_demodulation,[],[f29,f185])).

fof(f294,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1 ) ),
    inference(subsumption_resolution,[],[f293,f135])).

fof(f293,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f292,f73])).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(subsumption_resolution,[],[f291,f34])).

fof(f291,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X1,k1_xboole_0)
      | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1)
      | X0 = X1
      | ~ v2_funct_1(sK1) ) ),
    inference(superposition,[],[f40,f234])).

fof(f234,plain,(
    k1_xboole_0 = k1_relat_1(sK1) ),
    inference(forward_demodulation,[],[f233,f185])).

fof(f233,plain,(
    sK0 = k1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f197,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f197,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK1))
    | sK0 = k1_relat_1(sK1) ),
    inference(backward_demodulation,[],[f79,f185])).

fof(f79,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK1))
    | sK0 = k1_relat_1(sK1) ),
    inference(resolution,[],[f77,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f77,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(resolution,[],[f72,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (6804)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.45  % (6812)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (6815)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.49  % (6800)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.49  % (6807)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (6794)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (6799)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (6793)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (6793)Refutation not found, incomplete strategy% (6793)------------------------------
% 0.20/0.50  % (6793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6793)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6793)Memory used [KB]: 10618
% 0.20/0.50  % (6793)Time elapsed: 0.095 s
% 0.20/0.50  % (6793)------------------------------
% 0.20/0.50  % (6793)------------------------------
% 0.20/0.50  % (6798)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (6801)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (6810)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (6799)Refutation not found, incomplete strategy% (6799)------------------------------
% 0.20/0.50  % (6799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (6799)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (6799)Memory used [KB]: 10618
% 0.20/0.50  % (6799)Time elapsed: 0.061 s
% 0.20/0.50  % (6799)------------------------------
% 0.20/0.50  % (6799)------------------------------
% 0.20/0.50  % (6797)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (6818)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (6795)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (6817)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (6802)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (6806)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (6806)Refutation not found, incomplete strategy% (6806)------------------------------
% 0.20/0.51  % (6806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6806)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6806)Memory used [KB]: 6140
% 0.20/0.51  % (6806)Time elapsed: 0.121 s
% 0.20/0.51  % (6806)------------------------------
% 0.20/0.51  % (6806)------------------------------
% 0.20/0.52  % (6809)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (6796)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (6798)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f355,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f354,f139])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    sK2 != sK3),
% 0.20/0.52    inference(resolution,[],[f135,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ~v2_funct_1(sK1) | sK2 != sK3),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.52    inference(negated_conjecture,[],[f14])).
% 0.20/0.52  fof(f14,conjecture,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    v2_funct_1(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f134,f92])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f64,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f70,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f36,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | sK4(sK1) != sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f34,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sK4(X0) != sK5(X0) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    v1_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    v2_funct_1(sK1) | sK4(sK1) = sK5(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f132,f93])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))),
% 0.20/0.52    inference(resolution,[],[f63,f73])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f34,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f131])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    v2_funct_1(sK1) | k1_funct_1(sK1,sK4(sK1)) != k1_funct_1(sK1,sK5(sK1)) | sK4(sK1) = sK5(sK1) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f104,f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    r2_hidden(sK5(sK1),sK0) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f89,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(backward_demodulation,[],[f68,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.20/0.52    inference(resolution,[],[f36,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(resolution,[],[f36,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) | v2_funct_1(sK1) | r2_hidden(sK5(sK1),X1)) )),
% 0.20/0.52    inference(resolution,[],[f86,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f62,f73])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | r2_hidden(sK5(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f34,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK5(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | v2_funct_1(sK1) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK4(sK1) = X0) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    ( ! [X0] : (v2_funct_1(sK1) | ~r2_hidden(X0,sK0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,sK4(sK1)) | sK4(sK1) = X0 | v2_funct_1(sK1)) )),
% 0.20/0.52    inference(resolution,[],[f98,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | v2_funct_1(sK1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    r2_hidden(sK4(sK1),sK0) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f83,f72])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X1] : (~m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(X1)) | v2_funct_1(sK1) | r2_hidden(sK4(sK1),X1)) )),
% 0.20/0.52    inference(resolution,[],[f80,f46])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f61,f73])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | r2_hidden(sK4(sK1),k1_relat_1(sK1)) | v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f34,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(sK4(X0),k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f354,plain,(
% 0.20/0.52    sK2 = sK3),
% 0.20/0.52    inference(subsumption_resolution,[],[f349,f138])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.52    inference(resolution,[],[f135,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ~v2_funct_1(sK1) | k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f349,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3) | sK2 = sK3),
% 0.20/0.52    inference(resolution,[],[f330,f231])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f187,f135])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    r2_hidden(sK3,k1_xboole_0) | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f30,f185])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    k1_xboole_0 = sK0),
% 0.20/0.52    inference(subsumption_resolution,[],[f184,f139])).
% 0.20/0.52  fof(f184,plain,(
% 0.20/0.52    sK2 = sK3 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f177])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    sK2 = sK3 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.20/0.52    inference(superposition,[],[f172,f170])).
% 0.20/0.52  fof(f170,plain,(
% 0.20/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.20/0.52    inference(forward_demodulation,[],[f169,f138])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0),
% 0.20/0.52    inference(subsumption_resolution,[],[f168,f135])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f155,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ~sP6(sK1,sK0) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f66,f36])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f65,f34])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ~v1_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v2_funct_1(sK1) | k1_xboole_0 = sK0 | ~sP6(sK1,sK0)),
% 0.20/0.52    inference(resolution,[],[f35,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | k1_xboole_0 = X1 | ~sP6(X3,X0)) )),
% 0.20/0.52    inference(general_splitting,[],[f49,f59_D])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | sP6(X3,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f59_D])).
% 0.20/0.52  fof(f59_D,plain,(
% 0.20/0.52    ( ! [X0,X3] : (( ! [X2] : (~r2_hidden(X2,X0) | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) ) <=> ~sP6(X3,X0)) )),
% 0.20/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    ( ! [X3] : (sP6(X3,sK0) | sK3 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK3))) )),
% 0.20/0.52    inference(resolution,[],[f140,f59])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    r2_hidden(sK3,sK0)),
% 0.20/0.52    inference(resolution,[],[f135,f30])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0),
% 0.20/0.52    inference(subsumption_resolution,[],[f171,f135])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | k1_xboole_0 = sK0 | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f167,f67])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    ( ! [X3] : (sP6(X3,sK0) | sK2 = k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,sK2))) )),
% 0.20/0.52    inference(resolution,[],[f141,f59])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    r2_hidden(sK2,sK0)),
% 0.20/0.52    inference(resolution,[],[f135,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ~v2_funct_1(sK1) | r2_hidden(sK2,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ~v2_funct_1(sK1) | r2_hidden(sK3,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f330,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | k1_funct_1(sK1,sK2) != k1_funct_1(sK1,X0) | sK2 = X0) )),
% 0.20/0.52    inference(resolution,[],[f294,f230])).
% 0.20/0.52  fof(f230,plain,(
% 0.20/0.52    r2_hidden(sK2,k1_xboole_0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f186,f135])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    r2_hidden(sK2,k1_xboole_0) | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f29,f185])).
% 0.20/0.52  fof(f294,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f293,f135])).
% 0.20/0.52  fof(f293,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f292,f73])).
% 0.20/0.52  fof(f292,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f291,f34])).
% 0.20/0.52  fof(f291,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X1,k1_xboole_0) | k1_funct_1(sK1,X0) != k1_funct_1(sK1,X1) | X0 = X1 | ~v2_funct_1(sK1)) )),
% 0.20/0.52    inference(superposition,[],[f40,f234])).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    k1_xboole_0 = k1_relat_1(sK1)),
% 0.20/0.52    inference(forward_demodulation,[],[f233,f185])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    sK0 = k1_relat_1(sK1)),
% 0.20/0.52    inference(subsumption_resolution,[],[f197,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,k1_relat_1(sK1)) | sK0 = k1_relat_1(sK1)),
% 0.20/0.52    inference(backward_demodulation,[],[f79,f185])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ~r1_tarski(sK0,k1_relat_1(sK1)) | sK0 = k1_relat_1(sK1)),
% 0.20/0.52    inference(resolution,[],[f77,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.20/0.52    inference(resolution,[],[f72,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (6798)------------------------------
% 0.20/0.52  % (6798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (6798)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (6798)Memory used [KB]: 6268
% 0.20/0.52  % (6798)Time elapsed: 0.122 s
% 0.20/0.52  % (6798)------------------------------
% 0.20/0.52  % (6798)------------------------------
% 0.20/0.52  % (6792)Success in time 0.168 s
%------------------------------------------------------------------------------
