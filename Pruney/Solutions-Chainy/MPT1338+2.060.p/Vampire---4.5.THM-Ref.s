%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:09 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  168 (47452 expanded)
%              Number of leaves         :   22 (9498 expanded)
%              Depth                    :   29
%              Number of atoms          :  389 (247299 expanded)
%              Number of equality atoms :  122 (77927 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f797,plain,(
    $false ),
    inference(subsumption_resolution,[],[f738,f640])).

fof(f640,plain,(
    v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f639,f288])).

fof(f288,plain,(
    k2_relat_1(k1_xboole_0) = k2_relat_1(k2_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f244,f270,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f270,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),X0) ),
    inference(unit_resulting_resolution,[],[f251,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f251,plain,(
    ! [X1] : m1_subset_1(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(backward_demodulation,[],[f247,f246])).

fof(f246,plain,(
    ! [X0,X1] : k2_relat_1(k2_relat_1(k1_xboole_0)) = k2_relset_1(X0,X1,k2_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f196,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

% (1425)Refutation not found, incomplete strategy% (1425)------------------------------
% (1425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1425)Termination reason: Refutation not found, incomplete strategy

% (1425)Memory used [KB]: 10618
% (1425)Time elapsed: 0.119 s
% (1425)------------------------------
% (1425)------------------------------
fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f196,plain,(
    ! [X1] : m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1)) ),
    inference(superposition,[],[f184,f100])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f184,plain,(
    ! [X0,X1] : m1_subset_1(k2_relat_1(k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X1)) ),
    inference(forward_demodulation,[],[f181,f159])).

fof(f159,plain,(
    ! [X0,X1] : k2_relat_1(k2_zfmisc_1(X0,X1)) = k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f116,f89])).

fof(f116,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f97,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f181,plain,(
    ! [X0,X1] : m1_subset_1(k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X1)) ),
    inference(unit_resulting_resolution,[],[f116,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f247,plain,(
    ! [X0,X1] : m1_subset_1(k2_relset_1(X0,X1,k2_relat_1(k1_xboole_0)),k1_zfmisc_1(X1)) ),
    inference(unit_resulting_resolution,[],[f196,f90])).

fof(f244,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k1_xboole_0),X0) ),
    inference(unit_resulting_resolution,[],[f196,f84])).

fof(f639,plain,(
    v1_xboole_0(k2_relat_1(k2_relat_1(k1_xboole_0))) ),
    inference(forward_demodulation,[],[f638,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f638,plain,(
    ! [X0] : v1_xboole_0(k2_relat_1(k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f637,f99])).

fof(f637,plain,(
    ! [X0,X1] : v1_xboole_0(k2_relat_1(k2_relat_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k1_xboole_0))))) ),
    inference(forward_demodulation,[],[f603,f604])).

fof(f604,plain,(
    k1_xboole_0 = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f585,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f585,plain,(
    v1_xboole_0(k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f345,f344,f343,f561,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

% (1426)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f561,plain,(
    ~ v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f358,f357,f560,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f560,plain,(
    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f514,f354])).

fof(f354,plain,(
    k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f343,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f514,plain,(
    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f511])).

fof(f511,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f361,f508])).

fof(f508,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f507,f253])).

fof(f253,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f252,f212])).

fof(f212,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f140,f208])).

fof(f208,plain,(
    k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f122,f127,f207,f79])).

fof(f207,plain,(
    v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f57,f168,f166,f165,f72])).

fof(f165,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f111,f163])).

fof(f163,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f110,f160])).

fof(f160,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f111,f89])).

fof(f110,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f108,f103])).

fof(f103,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f63,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f63,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f108,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f60,f104])).

fof(f104,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f64,f65])).

fof(f64,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f111,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f107,f103])).

fof(f107,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f59,f104])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f28])).

fof(f166,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f112,f163])).

fof(f112,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f106,f103])).

fof(f106,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f58,f104])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f168,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f115,f163])).

fof(f115,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f62,f63,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f127,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f111,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f122,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f71,f111,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f140,plain,(
    k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2) ),
    inference(superposition,[],[f132,f136])).

fof(f136,plain,(
    sK2 = k7_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f122,f127,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f132,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(unit_resulting_resolution,[],[f122,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f252,plain,(
    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f61,f57,f122,f97,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

fof(f61,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f507,plain,(
    k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f362,f366])).

fof(f366,plain,(
    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f358,f357,f77])).

fof(f362,plain,(
    ! [X0] : k9_relat_1(k2_funct_1(sK2),X0) = k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) ),
    inference(unit_resulting_resolution,[],[f358,f73])).

fof(f361,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f348,f355])).

fof(f355,plain,(
    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f343,f89])).

fof(f348,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f347,f342])).

fof(f342,plain,(
    k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(unit_resulting_resolution,[],[f61,f57,f214,f213,f217,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f217,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f171,f208])).

fof(f171,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f160,f163])).

fof(f213,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f165,f208])).

fof(f214,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f166,f208])).

fof(f347,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    inference(backward_demodulation,[],[f220,f342])).

fof(f220,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f218,f208])).

fof(f218,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(backward_demodulation,[],[f172,f208])).

fof(f172,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(forward_demodulation,[],[f167,f163])).

fof(f167,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f114,f163])).

fof(f114,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f113,f103])).

fof(f113,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f109,f103])).

fof(f109,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f105,f104])).

fof(f105,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f56,f104])).

fof(f56,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f357,plain,(
    v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f343,f91])).

fof(f358,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f71,f343,f66])).

fof(f343,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f57,f61,f214,f213,f217,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f344,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f57,f61,f214,f213,f217,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f345,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f57,f61,f214,f213,f217,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f603,plain,(
    ! [X0,X1] : v1_xboole_0(k2_relat_1(k2_relat_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k1_relat_1(sK2)))))) ),
    inference(unit_resulting_resolution,[],[f199,f585,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f199,plain,(
    ! [X2,X0,X1] : m1_subset_1(k2_relat_1(k2_relat_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X1)) ),
    inference(forward_demodulation,[],[f189,f190])).

fof(f190,plain,(
    ! [X2,X0,X1] : k2_relset_1(X0,X1,k2_relat_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))) = k2_relat_1(k2_relat_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))) ),
    inference(unit_resulting_resolution,[],[f184,f89])).

fof(f189,plain,(
    ! [X2,X0,X1] : m1_subset_1(k2_relset_1(X0,X1,k2_relat_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X1)) ),
    inference(unit_resulting_resolution,[],[f184,f90])).

fof(f738,plain,(
    ~ v1_xboole_0(k2_relat_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f168,f731])).

fof(f731,plain,(
    k1_xboole_0 = sK2 ),
    inference(unit_resulting_resolution,[],[f592,f67])).

fof(f592,plain,(
    v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f213,f585,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n019.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 13:28:37 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.44  % (1432)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.46  % (1428)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.46  % (1448)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.48  % (1443)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.48  % (1432)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.49  % (1433)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.49  % (1425)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f797,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f738,f640])).
% 0.19/0.50  fof(f640,plain,(
% 0.19/0.50    v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 0.19/0.50    inference(forward_demodulation,[],[f639,f288])).
% 0.19/0.50  fof(f288,plain,(
% 0.19/0.50    k2_relat_1(k1_xboole_0) = k2_relat_1(k2_relat_1(k1_xboole_0))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f244,f270,f82])).
% 0.19/0.50  fof(f82,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.50  fof(f270,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(k2_relat_1(k1_xboole_0)),X0)) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f251,f84])).
% 0.19/0.50  fof(f84,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.50  fof(f251,plain,(
% 0.19/0.50    ( ! [X1] : (m1_subset_1(k2_relat_1(k2_relat_1(k1_xboole_0)),k1_zfmisc_1(X1))) )),
% 0.19/0.50    inference(backward_demodulation,[],[f247,f246])).
% 0.19/0.50  fof(f246,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_relat_1(k2_relat_1(k1_xboole_0)) = k2_relset_1(X0,X1,k2_relat_1(k1_xboole_0))) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f196,f89])).
% 0.19/0.50  fof(f89,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f49])).
% 0.19/0.50  % (1425)Refutation not found, incomplete strategy% (1425)------------------------------
% 0.19/0.50  % (1425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (1425)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (1425)Memory used [KB]: 10618
% 0.19/0.50  % (1425)Time elapsed: 0.119 s
% 0.19/0.50  % (1425)------------------------------
% 0.19/0.50  % (1425)------------------------------
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.50  fof(f196,plain,(
% 0.19/0.50    ( ! [X1] : (m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X1))) )),
% 0.19/0.50    inference(superposition,[],[f184,f100])).
% 0.19/0.50  fof(f100,plain,(
% 0.19/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.50    inference(equality_resolution,[],[f86])).
% 0.19/0.50  fof(f86,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.50  fof(f184,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(k2_relat_1(k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X1))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f181,f159])).
% 0.19/0.50  fof(f159,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f116,f89])).
% 0.19/0.50  fof(f116,plain,(
% 0.19/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f97,f83])).
% 0.19/0.50  fof(f83,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f5])).
% 0.19/0.50  fof(f97,plain,(
% 0.19/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.50    inference(equality_resolution,[],[f81])).
% 0.19/0.50  fof(f81,plain,(
% 0.19/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f181,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,k2_zfmisc_1(X0,X1)),k1_zfmisc_1(X1))) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f116,f90])).
% 0.19/0.50  fof(f90,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f50])).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.19/0.50  fof(f247,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,k2_relat_1(k1_xboole_0)),k1_zfmisc_1(X1))) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f196,f90])).
% 0.19/0.50  fof(f244,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0)) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f196,f84])).
% 0.19/0.50  fof(f639,plain,(
% 0.19/0.50    v1_xboole_0(k2_relat_1(k2_relat_1(k1_xboole_0)))),
% 0.19/0.50    inference(forward_demodulation,[],[f638,f99])).
% 0.19/0.50  fof(f99,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.50    inference(equality_resolution,[],[f87])).
% 0.19/0.50  fof(f87,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f638,plain,(
% 0.19/0.50    ( ! [X0] : (v1_xboole_0(k2_relat_1(k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0))))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f637,f99])).
% 0.19/0.50  fof(f637,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v1_xboole_0(k2_relat_1(k2_relat_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k1_xboole_0)))))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f603,f604])).
% 0.19/0.50  fof(f604,plain,(
% 0.19/0.50    k1_xboole_0 = k1_relat_1(sK2)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f585,f67])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f31])).
% 0.19/0.50  fof(f31,plain,(
% 0.19/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.19/0.50  fof(f585,plain,(
% 0.19/0.50    v1_xboole_0(k1_relat_1(sK2))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f345,f344,f343,f561,f72])).
% 0.19/0.50  fof(f72,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f38])).
% 0.19/0.50  fof(f38,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.50    inference(flattening,[],[f37])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f17])).
% 0.19/0.50  % (1426)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  fof(f17,axiom,(
% 0.19/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.19/0.50  fof(f561,plain,(
% 0.19/0.50    ~v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f358,f357,f560,f79])).
% 0.19/0.50  fof(f79,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(flattening,[],[f46])).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,axiom,(
% 0.19/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.19/0.50  fof(f560,plain,(
% 0.19/0.50    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))),
% 0.19/0.50    inference(superposition,[],[f514,f354])).
% 0.19/0.50  fof(f354,plain,(
% 0.19/0.50    k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f343,f88])).
% 0.19/0.50  fof(f88,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f48])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f15])).
% 0.19/0.50  fof(f15,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.19/0.50  fof(f514,plain,(
% 0.19/0.50    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f511])).
% 0.19/0.50  fof(f511,plain,(
% 0.19/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f361,f508])).
% 0.19/0.50  fof(f508,plain,(
% 0.19/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.19/0.50    inference(forward_demodulation,[],[f507,f253])).
% 0.19/0.50  fof(f253,plain,(
% 0.19/0.50    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.19/0.50    inference(forward_demodulation,[],[f252,f212])).
% 0.19/0.50  fof(f212,plain,(
% 0.19/0.50    k2_relat_1(sK2) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f140,f208])).
% 0.19/0.50  fof(f208,plain,(
% 0.19/0.50    k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f122,f127,f207,f79])).
% 0.19/0.50  fof(f207,plain,(
% 0.19/0.50    v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f57,f168,f166,f165,f72])).
% 0.19/0.50  fof(f165,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.19/0.50    inference(backward_demodulation,[],[f111,f163])).
% 0.19/0.50  fof(f163,plain,(
% 0.19/0.50    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.19/0.50    inference(backward_demodulation,[],[f110,f160])).
% 0.19/0.50  fof(f160,plain,(
% 0.19/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f111,f89])).
% 0.19/0.50  fof(f110,plain,(
% 0.19/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.19/0.50    inference(backward_demodulation,[],[f108,f103])).
% 0.19/0.50  fof(f103,plain,(
% 0.19/0.50    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f63,f65])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f29])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f21])).
% 0.19/0.50  fof(f21,axiom,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    l1_struct_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f25])).
% 0.19/0.50  fof(f25,negated_conjecture,(
% 0.19/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.19/0.50    inference(negated_conjecture,[],[f24])).
% 0.19/0.50  fof(f24,conjecture,(
% 0.19/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.19/0.50  fof(f108,plain,(
% 0.19/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.19/0.50    inference(backward_demodulation,[],[f60,f104])).
% 0.19/0.50  fof(f104,plain,(
% 0.19/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f64,f65])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    l1_struct_0(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f60,plain,(
% 0.19/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f111,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.19/0.50    inference(backward_demodulation,[],[f107,f103])).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.50    inference(backward_demodulation,[],[f59,f104])).
% 0.19/0.50  fof(f59,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f166,plain,(
% 0.19/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f112,f163])).
% 0.19/0.50  fof(f112,plain,(
% 0.19/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.19/0.50    inference(backward_demodulation,[],[f106,f103])).
% 0.19/0.50  fof(f106,plain,(
% 0.19/0.50    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.50    inference(backward_demodulation,[],[f58,f104])).
% 0.19/0.50  fof(f58,plain,(
% 0.19/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f168,plain,(
% 0.19/0.50    ~v1_xboole_0(k2_relat_1(sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f115,f163])).
% 0.19/0.50  fof(f115,plain,(
% 0.19/0.50    ~v1_xboole_0(k2_struct_0(sK1))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f62,f63,f69])).
% 0.19/0.50  fof(f69,plain,(
% 0.19/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f34])).
% 0.19/0.50  fof(f34,plain,(
% 0.19/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f33])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f22])).
% 0.19/0.50  fof(f22,axiom,(
% 0.19/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.19/0.50  fof(f62,plain,(
% 0.19/0.50    ~v2_struct_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    v1_funct_1(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f127,plain,(
% 0.19/0.50    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f111,f91])).
% 0.19/0.50  fof(f91,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f51])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.50    inference(ennf_transformation,[],[f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.19/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.19/0.50  fof(f11,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.50  fof(f122,plain,(
% 0.19/0.50    v1_relat_1(sK2)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f71,f111,f66])).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.50  fof(f140,plain,(
% 0.19/0.50    k9_relat_1(sK2,k2_struct_0(sK0)) = k2_relat_1(sK2)),
% 0.19/0.50    inference(superposition,[],[f132,f136])).
% 0.19/0.50  fof(f136,plain,(
% 0.19/0.50    sK2 = k7_relat_1(sK2,k2_struct_0(sK0))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f122,f127,f77])).
% 0.19/0.50  fof(f77,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f45])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(flattening,[],[f44])).
% 0.19/0.50  fof(f44,plain,(
% 0.19/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,axiom,(
% 0.19/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 0.19/0.50  fof(f132,plain,(
% 0.19/0.50    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f122,f73])).
% 0.19/0.50  fof(f73,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f39])).
% 0.19/0.50  fof(f39,plain,(
% 0.19/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.50    inference(ennf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.19/0.50  fof(f252,plain,(
% 0.19/0.50    k1_relat_1(sK2) = k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2)))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f61,f57,f122,f97,f70])).
% 0.19/0.50  fof(f70,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r1_tarski(X1,k1_relat_1(X0)) | k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.50    inference(flattening,[],[f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).
% 0.19/0.50  fof(f61,plain,(
% 0.19/0.50    v2_funct_1(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f507,plain,(
% 0.19/0.50    k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2))),
% 0.19/0.50    inference(superposition,[],[f362,f366])).
% 0.19/0.50  fof(f366,plain,(
% 0.19/0.50    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f358,f357,f77])).
% 0.19/0.50  fof(f362,plain,(
% 0.19/0.50    ( ! [X0] : (k9_relat_1(k2_funct_1(sK2),X0) = k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0))) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f358,f73])).
% 0.19/0.50  fof(f361,plain,(
% 0.19/0.50    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f348,f355])).
% 0.19/0.50  fof(f355,plain,(
% 0.19/0.50    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f343,f89])).
% 0.19/0.50  fof(f348,plain,(
% 0.19/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.19/0.50    inference(forward_demodulation,[],[f347,f342])).
% 0.19/0.50  fof(f342,plain,(
% 0.19/0.50    k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f61,f57,f214,f213,f217,f95])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.50    inference(flattening,[],[f54])).
% 0.19/0.50  fof(f54,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.50    inference(ennf_transformation,[],[f23])).
% 0.19/0.50  fof(f23,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.19/0.50  fof(f217,plain,(
% 0.19/0.50    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.19/0.50    inference(backward_demodulation,[],[f171,f208])).
% 0.19/0.50  fof(f171,plain,(
% 0.19/0.50    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.19/0.50    inference(backward_demodulation,[],[f160,f163])).
% 0.19/0.50  fof(f213,plain,(
% 0.19/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.19/0.50    inference(backward_demodulation,[],[f165,f208])).
% 0.19/0.50  fof(f214,plain,(
% 0.19/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f166,f208])).
% 0.19/0.50  fof(f347,plain,(
% 0.19/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f220,f342])).
% 0.19/0.50  fof(f220,plain,(
% 0.19/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.19/0.50    inference(forward_demodulation,[],[f218,f208])).
% 0.19/0.50  fof(f218,plain,(
% 0.19/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f172,f208])).
% 0.19/0.50  fof(f172,plain,(
% 0.19/0.50    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.19/0.50    inference(forward_demodulation,[],[f167,f163])).
% 0.19/0.50  fof(f167,plain,(
% 0.19/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f114,f163])).
% 0.19/0.50  fof(f114,plain,(
% 0.19/0.50    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.19/0.50    inference(forward_demodulation,[],[f113,f103])).
% 0.19/0.50  fof(f113,plain,(
% 0.19/0.50    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f109,f103])).
% 0.19/0.50  fof(f109,plain,(
% 0.19/0.50    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.50    inference(forward_demodulation,[],[f105,f104])).
% 0.19/0.50  fof(f105,plain,(
% 0.19/0.50    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.50    inference(backward_demodulation,[],[f56,f104])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f28])).
% 0.19/0.50  fof(f357,plain,(
% 0.19/0.50    v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f343,f91])).
% 0.19/0.50  fof(f358,plain,(
% 0.19/0.50    v1_relat_1(k2_funct_1(sK2))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f71,f343,f66])).
% 0.19/0.50  fof(f343,plain,(
% 0.19/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f57,f61,f214,f213,f217,f94])).
% 0.19/0.50  fof(f94,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f53])).
% 0.19/0.50  fof(f53,plain,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.19/0.50    inference(flattening,[],[f52])).
% 0.19/0.50  fof(f52,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.19/0.50    inference(ennf_transformation,[],[f20])).
% 0.19/0.50  fof(f20,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.19/0.50  fof(f344,plain,(
% 0.19/0.50    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f57,f61,f214,f213,f217,f93])).
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f53])).
% 0.19/0.50  fof(f345,plain,(
% 0.19/0.50    v1_funct_1(k2_funct_1(sK2))),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f57,f61,f214,f213,f217,f92])).
% 0.19/0.50  fof(f92,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f53])).
% 0.19/0.50  fof(f603,plain,(
% 0.19/0.50    ( ! [X0,X1] : (v1_xboole_0(k2_relat_1(k2_relat_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k1_relat_1(sK2))))))) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f199,f585,f68])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.19/0.50  fof(f199,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(k2_relat_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X1))) )),
% 0.19/0.50    inference(forward_demodulation,[],[f189,f190])).
% 0.19/0.50  fof(f190,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,k2_relat_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))) = k2_relat_1(k2_relat_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1))))) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f184,f89])).
% 0.19/0.50  fof(f189,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,k2_relat_1(k2_zfmisc_1(X2,k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X1))) )),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f184,f90])).
% 0.19/0.50  fof(f738,plain,(
% 0.19/0.50    ~v1_xboole_0(k2_relat_1(k1_xboole_0))),
% 0.19/0.50    inference(backward_demodulation,[],[f168,f731])).
% 0.19/0.50  fof(f731,plain,(
% 0.19/0.50    k1_xboole_0 = sK2),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f592,f67])).
% 0.19/0.50  fof(f592,plain,(
% 0.19/0.50    v1_xboole_0(sK2)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f213,f585,f75])).
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f41])).
% 0.19/0.50  fof(f41,plain,(
% 0.19/0.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,axiom,(
% 0.19/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (1432)------------------------------
% 0.19/0.50  % (1432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (1432)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (1432)Memory used [KB]: 2174
% 0.19/0.50  % (1432)Time elapsed: 0.097 s
% 0.19/0.50  % (1432)------------------------------
% 0.19/0.50  % (1432)------------------------------
% 0.19/0.50  % (1423)Success in time 0.164 s
%------------------------------------------------------------------------------
