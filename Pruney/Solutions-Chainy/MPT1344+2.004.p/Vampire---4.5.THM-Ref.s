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
% DateTime   : Thu Dec  3 13:14:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 411 expanded)
%              Number of leaves         :   16 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          :  281 (2037 expanded)
%              Number of equality atoms :   64 ( 493 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f194,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f78,f88,f135,f138,f193])).

fof(f193,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_8 ),
    inference(trivial_inequality_removal,[],[f191])).

fof(f191,plain,
    ( k10_relat_1(sK2,sK3) != k10_relat_1(sK2,sK3)
    | ~ spl4_8 ),
    inference(superposition,[],[f120,f190])).

fof(f190,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f168,f134])).

fof(f134,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl4_8
  <=> ! [X0] : k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f168,plain,(
    ! [X0] : k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0) ),
    inference(global_subsumption,[],[f33,f58,f167])).

fof(f167,plain,(
    ! [X0] :
      ( k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v1_funct_1(sK2) ) ),
    inference(forward_demodulation,[],[f165,f119])).

fof(f119,plain,(
    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_subsumption,[],[f31,f33,f58,f59,f118])).

fof(f118,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f117])).

fof(f117,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(superposition,[],[f49,f60])).

fof(f60,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f54,f53])).

fof(f53,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f38,f37])).

fof(f37,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_funct_1(X2)
                        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                     => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f54,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f30,f52])).

fof(f52,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f38,f36])).

fof(f36,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f55,f53])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f35,f52])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f31,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f165,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),X0) = k9_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),X0) ) ),
    inference(resolution,[],[f111,f59])).

fof(f111,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
      | ~ v1_funct_2(X7,X8,X9)
      | ~ v1_funct_1(X7)
      | k7_relset_1(X9,X8,k2_tops_2(X8,X9,X7),X10) = k9_relat_1(k2_tops_2(X8,X9,X7),X10) ) ),
    inference(resolution,[],[f48,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f58,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f56,f53])).

fof(f56,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f34,f52])).

fof(f34,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f120,plain,(
    k10_relat_1(sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) ),
    inference(backward_demodulation,[],[f105,f119])).

fof(f105,plain,(
    k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k10_relat_1(sK2,sK3) ),
    inference(backward_demodulation,[],[f80,f102])).

fof(f102,plain,(
    ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f51,f59])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f80,plain,(
    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    inference(forward_demodulation,[],[f79,f53])).

fof(f79,plain,(
    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    inference(forward_demodulation,[],[f32,f52])).

fof(f32,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f138,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f131,f33])).

fof(f131,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f135,plain,
    ( ~ spl4_3
    | ~ spl4_7
    | spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f128,f85,f133,f130,f71])).

fof(f71,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f85,plain,
    ( spl4_5
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f128,plain,
    ( ! [X0] :
        ( k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f126,f86])).

fof(f86,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK2)),X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f97,f31])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f40,f41,f91])).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f45,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f88,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f83,f71,f85])).

fof(f83,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(global_subsumption,[],[f33,f81])).

fof(f81,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f43,f31])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f78,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f75,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f75,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f76,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f62,f74,f71])).

fof(f62,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f39,f59])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (31236)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (31244)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.49  % (31236)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f76,f78,f88,f135,f138,f193])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ~spl4_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    $false | ~spl4_8),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    k10_relat_1(sK2,sK3) != k10_relat_1(sK2,sK3) | ~spl4_8),
% 0.21/0.49    inference(superposition,[],[f120,f190])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ( ! [X0] : (k10_relat_1(sK2,X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)) ) | ~spl4_8),
% 0.21/0.49    inference(forward_demodulation,[],[f168,f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)) ) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f133])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl4_8 <=> ! [X0] : k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0)) )),
% 0.21/0.49    inference(global_subsumption,[],[f33,f58,f167])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X0) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f165,f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.49    inference(global_subsumption,[],[f31,f33,f58,f59,f118])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.49    inference(superposition,[],[f49,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f54,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f38,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    l1_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f30,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f38,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    l1_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.49    inference(forward_demodulation,[],[f55,f53])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.49    inference(backward_demodulation,[],[f35,f52])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    v2_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),X0) = k9_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),X0)) )),
% 0.21/0.49    inference(resolution,[],[f111,f59])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X10,X8,X7,X9] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(X7,X8,X9) | ~v1_funct_1(X7) | k7_relset_1(X9,X8,k2_tops_2(X8,X9,X7),X10) = k9_relat_1(k2_tops_2(X8,X9,X7),X10)) )),
% 0.21/0.49    inference(resolution,[],[f48,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.49    inference(forward_demodulation,[],[f56,f53])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.49    inference(backward_demodulation,[],[f34,f52])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    k10_relat_1(sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3)),
% 0.21/0.49    inference(backward_demodulation,[],[f105,f119])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) != k10_relat_1(sK2,sK3)),
% 0.21/0.49    inference(backward_demodulation,[],[f80,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.21/0.49    inference(resolution,[],[f51,f59])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.21/0.49    inference(forward_demodulation,[],[f79,f53])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.21/0.49    inference(forward_demodulation,[],[f32,f52])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    $false | spl4_7),
% 0.21/0.49    inference(resolution,[],[f131,f33])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl4_7 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ~spl4_3 | ~spl4_7 | spl4_8 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f128,f85,f133,f130,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl4_3 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl4_5 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_5),
% 0.21/0.49    inference(forward_demodulation,[],[f126,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_funct_1(sK2) | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(k2_funct_1(k2_funct_1(sK2)),X0) | ~v1_relat_1(sK2)) )),
% 0.21/0.49    inference(resolution,[],[f97,f31])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(global_subsumption,[],[f40,f41,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | k9_relat_1(k2_funct_1(X1),X2) = k10_relat_1(k2_funct_1(k2_funct_1(X1)),X2) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(resolution,[],[f45,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_funct_1)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    spl4_5 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f83,f71,f85])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    inference(global_subsumption,[],[f33,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    inference(resolution,[],[f43,f31])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl4_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    $false | spl4_4),
% 0.21/0.50    inference(resolution,[],[f75,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl4_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl4_4 <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    spl4_3 | ~spl4_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f62,f74,f71])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2)),
% 0.21/0.50    inference(resolution,[],[f39,f59])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (31236)------------------------------
% 0.21/0.50  % (31236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31236)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (31236)Memory used [KB]: 10746
% 0.21/0.50  % (31236)Time elapsed: 0.073 s
% 0.21/0.50  % (31236)------------------------------
% 0.21/0.50  % (31236)------------------------------
% 0.21/0.50  % (31223)Success in time 0.142 s
%------------------------------------------------------------------------------
