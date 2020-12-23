%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:20 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  215 (1798494 expanded)
%              Number of leaves         :   15 (317950 expanded)
%              Depth                    :   48
%              Number of atoms          :  611 (8843221 expanded)
%              Number of equality atoms :  197 (1572396 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1376,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1356,f1299])).

fof(f1299,plain,(
    r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1020,f1284])).

fof(f1284,plain,(
    k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1272,f1020])).

fof(f1272,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(superposition,[],[f1013,f1038])).

fof(f1038,plain,
    ( k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(backward_demodulation,[],[f947,f995])).

fof(f995,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f993,f852])).

fof(f852,plain,
    ( r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f742,f788])).

fof(f788,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f772,f727])).

fof(f727,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f132,f722])).

fof(f722,plain,(
    k1_xboole_0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f720,f377])).

fof(f377,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f365,f165])).

fof(f165,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f164,f131])).

fof(f131,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f125,f129])).

fof(f129,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f98,f127])).

fof(f127,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f71,f99])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f94,f92])).

fof(f92,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f94,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f49,f91])).

fof(f91,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f55,f53])).

fof(f53,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f98,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f95,f92])).

fof(f95,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f50,f91])).

fof(f50,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f125,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(resolution,[],[f70,f99])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f164,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f162,f132])).

fof(f162,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(resolution,[],[f77,f133])).

fof(f133,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f99,f129])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f365,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(subsumption_resolution,[],[f364,f153])).

fof(f153,plain,(
    ! [X0,X1] : v1_funct_1(k2_tops_2(X0,X1,sK3(X0,X1))) ),
    inference(subsumption_resolution,[],[f152,f67])).

fof(f67,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK3(X0,X1))
      | v1_funct_1(k2_tops_2(X0,X1,sK3(X0,X1))) ) ),
    inference(subsumption_resolution,[],[f150,f68])).

fof(f68,plain,(
    ! [X0,X1] : v1_funct_2(sK3(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK3(X0,X1),X0,X1)
      | ~ v1_funct_1(sK3(X0,X1))
      | v1_funct_1(k2_tops_2(X0,X1,sK3(X0,X1))) ) ),
    inference(resolution,[],[f78,f65])).

fof(f65,plain,(
    ! [X0,X1] : m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_tops_2(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f364,plain,
    ( ~ v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),sK3(k2_relat_1(sK2),k2_struct_0(sK0))))
    | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(subsumption_resolution,[],[f360,f169])).

fof(f169,plain,(
    ! [X0,X1] : v1_funct_2(k2_tops_2(X0,X1,sK3(X0,X1)),X1,X0) ),
    inference(subsumption_resolution,[],[f168,f67])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK3(X0,X1))
      | v1_funct_2(k2_tops_2(X0,X1,sK3(X0,X1)),X1,X0) ) ),
    inference(subsumption_resolution,[],[f166,f68])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK3(X0,X1),X0,X1)
      | ~ v1_funct_1(sK3(X0,X1))
      | v1_funct_2(k2_tops_2(X0,X1,sK3(X0,X1)),X1,X0) ) ),
    inference(resolution,[],[f79,f65])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f360,plain,
    ( ~ v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),sK3(k2_relat_1(sK2),k2_struct_0(sK0))),k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),sK3(k2_relat_1(sK2),k2_struct_0(sK0))))
    | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    inference(resolution,[],[f233,f175])).

fof(f175,plain,(
    ! [X0,X1] : m1_subset_1(k2_tops_2(X0,X1,sK3(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ),
    inference(subsumption_resolution,[],[f174,f67])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK3(X0,X1))
      | m1_subset_1(k2_tops_2(X0,X1,sK3(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f172,f68])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK3(X0,X1),X0,X1)
      | ~ v1_funct_1(sK3(X0,X1))
      | m1_subset_1(k2_tops_2(X0,X1,sK3(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f80,f65])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f233,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
      | ~ v1_funct_2(X3,k2_struct_0(sK0),k2_relat_1(sK2))
      | ~ v1_funct_1(X3)
      | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ) ),
    inference(subsumption_resolution,[],[f232,f47])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f232,plain,(
    ! [X3] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_struct_0(sK0),k2_relat_1(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
      | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ) ),
    inference(subsumption_resolution,[],[f229,f132])).

fof(f229,plain,(
    ! [X3] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_struct_0(sK0),k2_relat_1(sK2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
      | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ) ),
    inference(resolution,[],[f85,f133])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f720,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f719])).

fof(f719,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f245,f499])).

fof(f499,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f498,f118])).

fof(f118,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f117,f107])).

fof(f107,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f69,f99])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f117,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f116,f47])).

fof(f116,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f61,f51])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f498,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f497,f403])).

fof(f403,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f261,f165])).

fof(f261,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f248,f124])).

fof(f124,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f123,f107])).

fof(f123,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f122,f47])).

fof(f122,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f63,f51])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f248,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f197,f71])).

fof(f197,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f196,f130])).

fof(f130,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f127,f129])).

fof(f196,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f195,f51])).

fof(f195,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f194,f47])).

fof(f194,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f190,f132])).

fof(f190,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f83,f133])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

% (7013)Refutation not found, incomplete strategy% (7013)------------------------------
% (7013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7028)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (7013)Termination reason: Refutation not found, incomplete strategy

% (7013)Memory used [KB]: 11257
% (7013)Time elapsed: 0.135 s
% (7013)------------------------------
% (7013)------------------------------
fof(f497,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f496,f244])).

fof(f244,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f188,f165])).

fof(f188,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f187,f130])).

fof(f187,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f186,f51])).

fof(f186,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f185,f47])).

fof(f185,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f181,f132])).

fof(f181,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    inference(resolution,[],[f82,f133])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f496,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f495,f115])).

fof(f115,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f114,f107])).

fof(f114,plain,
    ( ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f113,f47])).

fof(f113,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f58,f51])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f495,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f473,f109])).

fof(f109,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f104,f107])).

fof(f104,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f60,f47])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f473,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(resolution,[],[f259,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f259,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f197,f165])).

fof(f245,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(superposition,[],[f227,f165])).

fof(f227,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f134,f223])).

fof(f223,plain,(
    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f222,f51])).

fof(f222,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f221,f130])).

fof(f221,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f220,f47])).

fof(f220,plain,
    ( ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f216,f132])).

fof(f216,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(resolution,[],[f84,f133])).

fof(f134,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(backward_demodulation,[],[f97,f129])).

fof(f97,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f96,f92])).

fof(f96,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f52,f91])).

fof(f52,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f132,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f100,f129])).

fof(f100,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f93,f92])).

fof(f93,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f48,f91])).

fof(f48,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f772,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) ),
    inference(resolution,[],[f728,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f728,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f133,f722])).

fof(f742,plain,(
    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,sK2,sK2) ),
    inference(backward_demodulation,[],[f365,f722])).

fof(f993,plain,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f992])).

fof(f992,plain,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f801,f988])).

fof(f988,plain,
    ( sK2 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f958,f987])).

fof(f987,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f984])).

fof(f984,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f879,f804])).

fof(f804,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f726,f788])).

fof(f726,plain,(
    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f131,f722])).

fof(f879,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f860,f803])).

fof(f803,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f727,f788])).

fof(f860,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f802,f86])).

fof(f86,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f802,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f728,f788])).

fof(f958,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | sK2 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f740,f788])).

fof(f740,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | sK2 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f287,f722])).

fof(f287,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f286,f118])).

fof(f286,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f285,f261])).

fof(f285,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f284,f115])).

fof(f284,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f283,f109])).

fof(f283,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f257,f188])).

fof(f257,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f197,f84])).

fof(f801,plain,
    ( ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f733,f788])).

fof(f733,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f227,f722])).

fof(f947,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f930,f738])).

fof(f738,plain,(
    v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f265,f722])).

fof(f265,plain,(
    v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f264,f109])).

fof(f264,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f252,f188])).

fof(f252,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(resolution,[],[f197,f79])).

fof(f930,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0) ),
    inference(resolution,[],[f739,f88])).

fof(f739,plain,(
    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f267,f722])).

fof(f267,plain,(
    m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f266,f109])).

fof(f266,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(subsumption_resolution,[],[f253,f188])).

fof(f253,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(resolution,[],[f197,f80])).

fof(f1013,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f733,f995])).

fof(f1020,plain,(
    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f742,f995])).

fof(f1356,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1293,f1351])).

fof(f1351,plain,(
    k1_xboole_0 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1320,f1350])).

fof(f1350,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1287,f1349])).

fof(f1349,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1330,f1288])).

fof(f1288,plain,(
    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1008,f1284])).

fof(f1008,plain,(
    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f727,f995])).

fof(f1330,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f1289,f86])).

fof(f1289,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f1009,f1284])).

fof(f1009,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f728,f995])).

fof(f1287,plain,(
    k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f1007,f1284])).

fof(f1007,plain,(
    k1_relat_1(k1_xboole_0) = k1_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f726,f995])).

fof(f1320,plain,
    ( k1_xboole_0 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1312,f1284])).

fof(f1312,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f1061,f1284])).

fof(f1061,plain,
    ( k2_struct_0(sK0) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1019,f995])).

fof(f1019,plain,
    ( k2_struct_0(sK0) != k1_relat_1(k1_xboole_0)
    | sK2 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f740,f995])).

fof(f1293,plain,(
    ~ r2_funct_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f1013,f1284])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:22:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (7016)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (7030)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (7013)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (7022)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (7031)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (7029)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (7020)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (7018)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (7025)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (7023)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (7011)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (7026)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.54  % (7015)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (7032)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.54  % (7024)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (7027)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.54  % (7019)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.55  % (7032)Refutation not found, incomplete strategy% (7032)------------------------------
% 0.21/0.55  % (7032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7032)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7032)Memory used [KB]: 10618
% 0.21/0.55  % (7032)Time elapsed: 0.096 s
% 0.21/0.55  % (7032)------------------------------
% 0.21/0.55  % (7032)------------------------------
% 0.21/0.56  % (7017)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.56  % (7025)Refutation not found, incomplete strategy% (7025)------------------------------
% 0.21/0.56  % (7025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (7014)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.57  % (7025)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (7025)Memory used [KB]: 1918
% 0.21/0.57  % (7025)Time elapsed: 0.117 s
% 0.21/0.57  % (7025)------------------------------
% 0.21/0.57  % (7025)------------------------------
% 1.69/0.58  % (7029)Refutation found. Thanks to Tanya!
% 1.69/0.58  % SZS status Theorem for theBenchmark
% 1.69/0.58  % SZS output start Proof for theBenchmark
% 1.69/0.58  fof(f1376,plain,(
% 1.69/0.58    $false),
% 1.69/0.58    inference(subsumption_resolution,[],[f1356,f1299])).
% 1.69/0.58  fof(f1299,plain,(
% 1.69/0.58    r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.69/0.58    inference(backward_demodulation,[],[f1020,f1284])).
% 1.69/0.58  fof(f1284,plain,(
% 1.69/0.58    k1_xboole_0 = k2_struct_0(sK0)),
% 1.69/0.58    inference(subsumption_resolution,[],[f1272,f1020])).
% 1.69/0.58  fof(f1272,plain,(
% 1.69/0.58    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.69/0.58    inference(superposition,[],[f1013,f1038])).
% 1.69/0.58  fof(f1038,plain,(
% 1.69/0.58    k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.69/0.58    inference(backward_demodulation,[],[f947,f995])).
% 1.69/0.58  fof(f995,plain,(
% 1.69/0.58    k1_xboole_0 = sK2),
% 1.69/0.58    inference(subsumption_resolution,[],[f993,f852])).
% 1.69/0.58  fof(f852,plain,(
% 1.69/0.58    r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2) | k1_xboole_0 = sK2),
% 1.69/0.58    inference(superposition,[],[f742,f788])).
% 1.69/0.58  fof(f788,plain,(
% 1.69/0.58    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2),
% 1.69/0.58    inference(subsumption_resolution,[],[f772,f727])).
% 1.69/0.58  fof(f727,plain,(
% 1.69/0.58    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)),
% 1.69/0.58    inference(backward_demodulation,[],[f132,f722])).
% 1.69/0.58  fof(f722,plain,(
% 1.69/0.58    k1_xboole_0 = k2_relat_1(sK2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f720,f377])).
% 1.69/0.58  fof(f377,plain,(
% 1.69/0.58    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.69/0.58    inference(superposition,[],[f365,f165])).
% 1.69/0.58  fof(f165,plain,(
% 1.69/0.58    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.69/0.58    inference(forward_demodulation,[],[f164,f131])).
% 1.69/0.58  fof(f131,plain,(
% 1.69/0.58    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.69/0.58    inference(backward_demodulation,[],[f125,f129])).
% 1.69/0.58  fof(f129,plain,(
% 1.69/0.58    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.69/0.58    inference(backward_demodulation,[],[f98,f127])).
% 1.69/0.58  fof(f127,plain,(
% 1.69/0.58    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 1.69/0.58    inference(resolution,[],[f71,f99])).
% 1.69/0.58  fof(f99,plain,(
% 1.69/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.69/0.58    inference(backward_demodulation,[],[f94,f92])).
% 1.69/0.58  fof(f92,plain,(
% 1.69/0.58    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.69/0.58    inference(resolution,[],[f55,f54])).
% 1.69/0.58  fof(f54,plain,(
% 1.69/0.58    l1_struct_0(sK0)),
% 1.69/0.58    inference(cnf_transformation,[],[f22])).
% 1.69/0.58  fof(f22,plain,(
% 1.69/0.58    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.69/0.58    inference(flattening,[],[f21])).
% 1.69/0.58  fof(f21,plain,(
% 1.69/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 1.69/0.58    inference(ennf_transformation,[],[f18])).
% 1.69/0.58  fof(f18,plain,(
% 1.69/0.58    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.69/0.58    inference(pure_predicate_removal,[],[f17])).
% 1.69/0.58  fof(f17,negated_conjecture,(
% 1.69/0.58    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.69/0.58    inference(negated_conjecture,[],[f16])).
% 1.69/0.58  fof(f16,conjecture,(
% 1.69/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 1.69/0.58  fof(f55,plain,(
% 1.69/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f23])).
% 1.69/0.58  fof(f23,plain,(
% 1.69/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.69/0.58    inference(ennf_transformation,[],[f13])).
% 1.69/0.58  fof(f13,axiom,(
% 1.69/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.69/0.58  fof(f94,plain,(
% 1.69/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 1.69/0.58    inference(backward_demodulation,[],[f49,f91])).
% 1.69/0.58  fof(f91,plain,(
% 1.69/0.58    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.69/0.58    inference(resolution,[],[f55,f53])).
% 1.69/0.58  fof(f53,plain,(
% 1.69/0.58    l1_struct_0(sK1)),
% 1.69/0.58    inference(cnf_transformation,[],[f22])).
% 1.69/0.58  fof(f49,plain,(
% 1.69/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.69/0.58    inference(cnf_transformation,[],[f22])).
% 1.69/0.58  fof(f71,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f36])).
% 1.69/0.58  fof(f36,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.58    inference(ennf_transformation,[],[f7])).
% 1.69/0.58  fof(f7,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.69/0.58  fof(f98,plain,(
% 1.69/0.58    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.69/0.58    inference(backward_demodulation,[],[f95,f92])).
% 1.69/0.58  fof(f95,plain,(
% 1.69/0.58    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.69/0.58    inference(backward_demodulation,[],[f50,f91])).
% 1.69/0.58  fof(f50,plain,(
% 1.69/0.58    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.69/0.58    inference(cnf_transformation,[],[f22])).
% 1.69/0.58  fof(f125,plain,(
% 1.69/0.58    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.69/0.58    inference(resolution,[],[f70,f99])).
% 1.69/0.58  fof(f70,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f35])).
% 1.69/0.58  fof(f35,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.58    inference(ennf_transformation,[],[f6])).
% 1.69/0.58  fof(f6,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.69/0.58  fof(f164,plain,(
% 1.69/0.58    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f162,f132])).
% 1.69/0.58  fof(f162,plain,(
% 1.69/0.58    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.69/0.58    inference(resolution,[],[f77,f133])).
% 1.69/0.58  fof(f133,plain,(
% 1.69/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.69/0.58    inference(backward_demodulation,[],[f99,f129])).
% 1.69/0.58  fof(f77,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f38])).
% 1.69/0.58  fof(f38,plain,(
% 1.69/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.58    inference(flattening,[],[f37])).
% 1.69/0.58  fof(f37,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.58    inference(ennf_transformation,[],[f8])).
% 1.69/0.58  fof(f8,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.69/0.58  fof(f365,plain,(
% 1.69/0.58    r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f364,f153])).
% 1.69/0.58  fof(f153,plain,(
% 1.69/0.58    ( ! [X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,sK3(X0,X1)))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f152,f67])).
% 1.69/0.58  fof(f67,plain,(
% 1.69/0.58    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f20])).
% 1.69/0.58  fof(f20,plain,(
% 1.69/0.58    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.58    inference(pure_predicate_removal,[],[f19])).
% 1.69/0.58  fof(f19,plain,(
% 1.69/0.58    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.58    inference(pure_predicate_removal,[],[f9])).
% 1.69/0.58  fof(f9,axiom,(
% 1.69/0.58    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_2)).
% 1.69/0.58  fof(f152,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~v1_funct_1(sK3(X0,X1)) | v1_funct_1(k2_tops_2(X0,X1,sK3(X0,X1)))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f150,f68])).
% 1.69/0.58  fof(f68,plain,(
% 1.69/0.58    ( ! [X0,X1] : (v1_funct_2(sK3(X0,X1),X0,X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f20])).
% 1.69/0.58  fof(f150,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~v1_funct_2(sK3(X0,X1),X0,X1) | ~v1_funct_1(sK3(X0,X1)) | v1_funct_1(k2_tops_2(X0,X1,sK3(X0,X1)))) )),
% 1.69/0.58    inference(resolution,[],[f78,f65])).
% 1.69/0.58  fof(f65,plain,(
% 1.69/0.58    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f20])).
% 1.69/0.58  fof(f78,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_funct_1(k2_tops_2(X0,X1,X2))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f40])).
% 1.69/0.58  fof(f40,plain,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.69/0.58    inference(flattening,[],[f39])).
% 1.69/0.58  fof(f39,plain,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.69/0.58    inference(ennf_transformation,[],[f15])).
% 1.69/0.58  fof(f15,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 1.69/0.58  fof(f364,plain,(
% 1.69/0.58    ~v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),sK3(k2_relat_1(sK2),k2_struct_0(sK0)))) | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f360,f169])).
% 1.69/0.58  fof(f169,plain,(
% 1.69/0.58    ( ! [X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,sK3(X0,X1)),X1,X0)) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f168,f67])).
% 1.69/0.58  fof(f168,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~v1_funct_1(sK3(X0,X1)) | v1_funct_2(k2_tops_2(X0,X1,sK3(X0,X1)),X1,X0)) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f166,f68])).
% 1.69/0.58  fof(f166,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~v1_funct_2(sK3(X0,X1),X0,X1) | ~v1_funct_1(sK3(X0,X1)) | v1_funct_2(k2_tops_2(X0,X1,sK3(X0,X1)),X1,X0)) )),
% 1.69/0.58    inference(resolution,[],[f79,f65])).
% 1.69/0.58  fof(f79,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f40])).
% 1.69/0.58  fof(f360,plain,(
% 1.69/0.58    ~v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),sK3(k2_relat_1(sK2),k2_struct_0(sK0))),k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),sK3(k2_relat_1(sK2),k2_struct_0(sK0)))) | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 1.69/0.58    inference(resolution,[],[f233,f175])).
% 1.69/0.58  fof(f175,plain,(
% 1.69/0.58    ( ! [X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,sK3(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f174,f67])).
% 1.69/0.58  fof(f174,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~v1_funct_1(sK3(X0,X1)) | m1_subset_1(k2_tops_2(X0,X1,sK3(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f172,f68])).
% 1.69/0.58  fof(f172,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~v1_funct_2(sK3(X0,X1),X0,X1) | ~v1_funct_1(sK3(X0,X1)) | m1_subset_1(k2_tops_2(X0,X1,sK3(X0,X1)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.69/0.58    inference(resolution,[],[f80,f65])).
% 1.69/0.58  fof(f80,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f40])).
% 1.69/0.58  fof(f233,plain,(
% 1.69/0.58    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(X3,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(X3) | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f232,f47])).
% 1.69/0.58  fof(f47,plain,(
% 1.69/0.58    v1_funct_1(sK2)),
% 1.69/0.58    inference(cnf_transformation,[],[f22])).
% 1.69/0.58  fof(f232,plain,(
% 1.69/0.58    ( ! [X3] : (~v1_funct_1(sK2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f229,f132])).
% 1.69/0.58  fof(f229,plain,(
% 1.69/0.58    ( ! [X3] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k2_struct_0(sK0),k2_relat_1(sK2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)) )),
% 1.69/0.58    inference(resolution,[],[f85,f133])).
% 1.69/0.58  fof(f85,plain,(
% 1.69/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X2,X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f46])).
% 1.69/0.58  fof(f46,plain,(
% 1.69/0.58    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.69/0.58    inference(flattening,[],[f45])).
% 1.69/0.58  fof(f45,plain,(
% 1.69/0.58    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.69/0.58    inference(ennf_transformation,[],[f10])).
% 1.69/0.58  fof(f10,axiom,(
% 1.69/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 1.69/0.58  fof(f720,plain,(
% 1.69/0.58    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.69/0.58    inference(duplicate_literal_removal,[],[f719])).
% 1.69/0.58  fof(f719,plain,(
% 1.69/0.58    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.69/0.58    inference(superposition,[],[f245,f499])).
% 1.69/0.58  fof(f499,plain,(
% 1.69/0.58    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.69/0.58    inference(forward_demodulation,[],[f498,f118])).
% 1.69/0.58  fof(f118,plain,(
% 1.69/0.58    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f117,f107])).
% 1.69/0.58  fof(f107,plain,(
% 1.69/0.58    v1_relat_1(sK2)),
% 1.69/0.58    inference(resolution,[],[f69,f99])).
% 1.69/0.58  fof(f69,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f34])).
% 1.69/0.58  fof(f34,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.69/0.58    inference(ennf_transformation,[],[f5])).
% 1.69/0.58  fof(f5,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.69/0.58  fof(f117,plain,(
% 1.69/0.58    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f116,f47])).
% 1.69/0.58  fof(f116,plain,(
% 1.69/0.58    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(resolution,[],[f61,f51])).
% 1.69/0.58  fof(f51,plain,(
% 1.69/0.58    v2_funct_1(sK2)),
% 1.69/0.58    inference(cnf_transformation,[],[f22])).
% 1.69/0.58  fof(f61,plain,(
% 1.69/0.58    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 1.69/0.58    inference(cnf_transformation,[],[f29])).
% 1.69/0.58  fof(f29,plain,(
% 1.69/0.58    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.58    inference(flattening,[],[f28])).
% 1.69/0.58  fof(f28,plain,(
% 1.69/0.58    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.58    inference(ennf_transformation,[],[f4])).
% 1.69/0.58  fof(f4,axiom,(
% 1.69/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.69/0.58  fof(f498,plain,(
% 1.69/0.58    k1_xboole_0 = k2_relat_1(sK2) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f497,f403])).
% 1.69/0.58  fof(f403,plain,(
% 1.69/0.58    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.69/0.58    inference(superposition,[],[f261,f165])).
% 1.69/0.58  fof(f261,plain,(
% 1.69/0.58    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(forward_demodulation,[],[f248,f124])).
% 1.69/0.58  fof(f124,plain,(
% 1.69/0.58    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f123,f107])).
% 1.69/0.58  fof(f123,plain,(
% 1.69/0.58    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f122,f47])).
% 1.69/0.58  fof(f122,plain,(
% 1.69/0.58    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(resolution,[],[f63,f51])).
% 1.69/0.58  fof(f63,plain,(
% 1.69/0.58    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f31])).
% 1.69/0.58  fof(f31,plain,(
% 1.69/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.58    inference(flattening,[],[f30])).
% 1.69/0.58  fof(f30,plain,(
% 1.69/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.58    inference(ennf_transformation,[],[f3])).
% 1.69/0.58  fof(f3,axiom,(
% 1.69/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.69/0.58  fof(f248,plain,(
% 1.69/0.58    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(resolution,[],[f197,f71])).
% 1.69/0.58  fof(f197,plain,(
% 1.69/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.69/0.58    inference(subsumption_resolution,[],[f196,f130])).
% 1.69/0.58  fof(f130,plain,(
% 1.69/0.58    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.69/0.58    inference(backward_demodulation,[],[f127,f129])).
% 1.69/0.58  fof(f196,plain,(
% 1.69/0.58    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.69/0.58    inference(subsumption_resolution,[],[f195,f51])).
% 1.69/0.58  fof(f195,plain,(
% 1.69/0.58    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.69/0.58    inference(subsumption_resolution,[],[f194,f47])).
% 1.69/0.58  fof(f194,plain,(
% 1.69/0.58    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.69/0.58    inference(subsumption_resolution,[],[f190,f132])).
% 1.69/0.58  fof(f190,plain,(
% 1.69/0.58    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.69/0.58    inference(resolution,[],[f83,f133])).
% 1.69/0.58  fof(f83,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f42])).
% 1.69/0.58  fof(f42,plain,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.69/0.58    inference(flattening,[],[f41])).
% 1.69/0.58  fof(f41,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.69/0.58    inference(ennf_transformation,[],[f11])).
% 1.69/0.58  fof(f11,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.69/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.69/0.58  % (7013)Refutation not found, incomplete strategy% (7013)------------------------------
% 1.69/0.58  % (7013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (7028)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.69/0.59  % (7013)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (7013)Memory used [KB]: 11257
% 1.69/0.59  % (7013)Time elapsed: 0.135 s
% 1.69/0.59  % (7013)------------------------------
% 1.69/0.59  % (7013)------------------------------
% 1.69/0.59  fof(f497,plain,(
% 1.69/0.59    k1_xboole_0 = k2_relat_1(sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f496,f244])).
% 1.69/0.59  fof(f244,plain,(
% 1.69/0.59    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.69/0.59    inference(superposition,[],[f188,f165])).
% 1.69/0.59  fof(f188,plain,(
% 1.69/0.59    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.69/0.59    inference(subsumption_resolution,[],[f187,f130])).
% 1.69/0.59  fof(f187,plain,(
% 1.69/0.59    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.69/0.59    inference(subsumption_resolution,[],[f186,f51])).
% 1.69/0.59  fof(f186,plain,(
% 1.69/0.59    ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.69/0.59    inference(subsumption_resolution,[],[f185,f47])).
% 1.69/0.59  fof(f185,plain,(
% 1.69/0.59    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.69/0.59    inference(subsumption_resolution,[],[f181,f132])).
% 1.69/0.59  fof(f181,plain,(
% 1.69/0.59    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.69/0.59    inference(resolution,[],[f82,f133])).
% 1.69/0.59  fof(f82,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f42])).
% 1.69/0.59  fof(f496,plain,(
% 1.69/0.59    k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f495,f115])).
% 1.69/0.59  fof(f115,plain,(
% 1.69/0.59    v2_funct_1(k2_funct_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f114,f107])).
% 1.69/0.59  fof(f114,plain,(
% 1.69/0.59    ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f113,f47])).
% 1.69/0.59  fof(f113,plain,(
% 1.69/0.59    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 1.69/0.59    inference(resolution,[],[f58,f51])).
% 1.69/0.59  fof(f58,plain,(
% 1.69/0.59    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f25])).
% 1.69/0.59  fof(f25,plain,(
% 1.69/0.59    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.59    inference(flattening,[],[f24])).
% 1.69/0.59  fof(f24,plain,(
% 1.69/0.59    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f2])).
% 1.69/0.59  fof(f2,axiom,(
% 1.69/0.59    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.69/0.59  fof(f495,plain,(
% 1.69/0.59    k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f473,f109])).
% 1.69/0.59  fof(f109,plain,(
% 1.69/0.59    v1_funct_1(k2_funct_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f104,f107])).
% 1.69/0.59  fof(f104,plain,(
% 1.69/0.59    ~v1_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.69/0.59    inference(resolution,[],[f60,f47])).
% 1.69/0.59  fof(f60,plain,(
% 1.69/0.59    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f27])).
% 1.69/0.59  fof(f27,plain,(
% 1.69/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.59    inference(flattening,[],[f26])).
% 1.69/0.59  fof(f26,plain,(
% 1.69/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f1])).
% 1.69/0.59  fof(f1,axiom,(
% 1.69/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.69/0.59  fof(f473,plain,(
% 1.69/0.59    k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.69/0.59    inference(resolution,[],[f259,f84])).
% 1.69/0.59  fof(f84,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f44])).
% 1.69/0.59  fof(f44,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.69/0.59    inference(flattening,[],[f43])).
% 1.69/0.59  fof(f43,plain,(
% 1.69/0.59    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.69/0.59    inference(ennf_transformation,[],[f14])).
% 1.69/0.59  fof(f14,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 1.69/0.59  fof(f259,plain,(
% 1.69/0.59    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.69/0.59    inference(superposition,[],[f197,f165])).
% 1.69/0.59  fof(f245,plain,(
% 1.69/0.59    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | k1_xboole_0 = k2_relat_1(sK2)),
% 1.69/0.59    inference(superposition,[],[f227,f165])).
% 1.69/0.59  fof(f227,plain,(
% 1.69/0.59    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 1.69/0.59    inference(backward_demodulation,[],[f134,f223])).
% 1.69/0.59  fof(f223,plain,(
% 1.69/0.59    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.69/0.59    inference(subsumption_resolution,[],[f222,f51])).
% 1.69/0.59  fof(f222,plain,(
% 1.69/0.59    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.69/0.59    inference(subsumption_resolution,[],[f221,f130])).
% 1.69/0.59  fof(f221,plain,(
% 1.69/0.59    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.69/0.59    inference(subsumption_resolution,[],[f220,f47])).
% 1.69/0.59  fof(f220,plain,(
% 1.69/0.59    ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.69/0.59    inference(subsumption_resolution,[],[f216,f132])).
% 1.69/0.59  fof(f216,plain,(
% 1.69/0.59    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.69/0.59    inference(resolution,[],[f84,f133])).
% 1.69/0.59  fof(f134,plain,(
% 1.69/0.59    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 1.69/0.59    inference(backward_demodulation,[],[f97,f129])).
% 1.69/0.59  fof(f97,plain,(
% 1.69/0.59    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.69/0.59    inference(backward_demodulation,[],[f96,f92])).
% 1.69/0.59  fof(f96,plain,(
% 1.69/0.59    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.69/0.59    inference(backward_demodulation,[],[f52,f91])).
% 1.69/0.59  fof(f52,plain,(
% 1.69/0.59    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.69/0.59    inference(cnf_transformation,[],[f22])).
% 1.69/0.59  fof(f132,plain,(
% 1.69/0.59    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.69/0.59    inference(backward_demodulation,[],[f100,f129])).
% 1.69/0.59  fof(f100,plain,(
% 1.69/0.59    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.69/0.59    inference(backward_demodulation,[],[f93,f92])).
% 1.69/0.59  fof(f93,plain,(
% 1.69/0.59    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 1.69/0.59    inference(backward_demodulation,[],[f48,f91])).
% 1.69/0.59  fof(f48,plain,(
% 1.69/0.59    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.69/0.59    inference(cnf_transformation,[],[f22])).
% 1.69/0.59  fof(f772,plain,(
% 1.69/0.59    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2 | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)),
% 1.69/0.59    inference(resolution,[],[f728,f88])).
% 1.69/0.59  fof(f88,plain,(
% 1.69/0.59    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.69/0.59    inference(equality_resolution,[],[f73])).
% 1.69/0.59  fof(f73,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f38])).
% 1.69/0.59  fof(f728,plain,(
% 1.69/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 1.69/0.59    inference(backward_demodulation,[],[f133,f722])).
% 1.69/0.59  fof(f742,plain,(
% 1.69/0.59    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,sK2,sK2)),
% 1.69/0.59    inference(backward_demodulation,[],[f365,f722])).
% 1.69/0.59  fof(f993,plain,(
% 1.69/0.59    ~r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2) | k1_xboole_0 = sK2),
% 1.69/0.59    inference(duplicate_literal_removal,[],[f992])).
% 1.69/0.59  fof(f992,plain,(
% 1.69/0.59    ~r2_funct_2(k1_xboole_0,k1_xboole_0,sK2,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.69/0.59    inference(superposition,[],[f801,f988])).
% 1.69/0.59  fof(f988,plain,(
% 1.69/0.59    sK2 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | k1_xboole_0 = sK2),
% 1.69/0.59    inference(subsumption_resolution,[],[f958,f987])).
% 1.69/0.59  fof(f987,plain,(
% 1.69/0.59    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2),
% 1.69/0.59    inference(duplicate_literal_removal,[],[f984])).
% 1.69/0.59  fof(f984,plain,(
% 1.69/0.59    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK2),
% 1.69/0.59    inference(superposition,[],[f879,f804])).
% 1.69/0.59  fof(f804,plain,(
% 1.69/0.59    k1_relat_1(sK2) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 1.69/0.59    inference(superposition,[],[f726,f788])).
% 1.69/0.59  fof(f726,plain,(
% 1.69/0.59    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2)),
% 1.69/0.59    inference(backward_demodulation,[],[f131,f722])).
% 1.69/0.59  fof(f879,plain,(
% 1.69/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 = sK2),
% 1.69/0.59    inference(subsumption_resolution,[],[f860,f803])).
% 1.69/0.59  fof(f803,plain,(
% 1.69/0.59    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = sK2),
% 1.69/0.59    inference(superposition,[],[f727,f788])).
% 1.69/0.59  fof(f860,plain,(
% 1.69/0.59    k1_xboole_0 = sK2 | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    inference(resolution,[],[f802,f86])).
% 1.69/0.59  fof(f86,plain,(
% 1.69/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.69/0.59    inference(equality_resolution,[],[f75])).
% 1.69/0.59  fof(f75,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f38])).
% 1.69/0.59  fof(f802,plain,(
% 1.69/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 = sK2),
% 1.69/0.59    inference(superposition,[],[f728,f788])).
% 1.69/0.59  fof(f958,plain,(
% 1.69/0.59    k1_xboole_0 != k1_relat_1(sK2) | sK2 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)) | k1_xboole_0 = sK2),
% 1.69/0.59    inference(superposition,[],[f740,f788])).
% 1.69/0.59  fof(f740,plain,(
% 1.69/0.59    k2_struct_0(sK0) != k1_relat_1(sK2) | sK2 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.59    inference(backward_demodulation,[],[f287,f722])).
% 1.69/0.59  fof(f287,plain,(
% 1.69/0.59    k2_struct_0(sK0) != k1_relat_1(sK2) | sK2 = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.59    inference(forward_demodulation,[],[f286,f118])).
% 1.69/0.59  fof(f286,plain,(
% 1.69/0.59    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.59    inference(forward_demodulation,[],[f285,f261])).
% 1.69/0.59  fof(f285,plain,(
% 1.69/0.59    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f284,f115])).
% 1.69/0.59  fof(f284,plain,(
% 1.69/0.59    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f283,f109])).
% 1.69/0.59  fof(f283,plain,(
% 1.69/0.59    ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f257,f188])).
% 1.69/0.59  fof(f257,plain,(
% 1.69/0.59    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.59    inference(resolution,[],[f197,f84])).
% 1.69/0.59  fof(f801,plain,(
% 1.69/0.59    ~r2_funct_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(sK2)),sK2) | k1_xboole_0 = sK2),
% 1.69/0.59    inference(superposition,[],[f733,f788])).
% 1.69/0.59  fof(f733,plain,(
% 1.69/0.59    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 1.69/0.59    inference(backward_demodulation,[],[f227,f722])).
% 1.69/0.59  fof(f947,plain,(
% 1.69/0.59    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f930,f738])).
% 1.69/0.59  fof(f738,plain,(
% 1.69/0.59    v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0)),
% 1.69/0.59    inference(backward_demodulation,[],[f265,f722])).
% 1.69/0.59  fof(f265,plain,(
% 1.69/0.59    v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f264,f109])).
% 1.69/0.59  fof(f264,plain,(
% 1.69/0.59    ~v1_funct_1(k2_funct_1(sK2)) | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.69/0.59    inference(subsumption_resolution,[],[f252,f188])).
% 1.69/0.59  fof(f252,plain,(
% 1.69/0.59    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.69/0.59    inference(resolution,[],[f197,f79])).
% 1.69/0.59  fof(f930,plain,(
% 1.69/0.59    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k1_xboole_0)),
% 1.69/0.59    inference(resolution,[],[f739,f88])).
% 1.69/0.59  fof(f739,plain,(
% 1.69/0.59    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 1.69/0.59    inference(backward_demodulation,[],[f267,f722])).
% 1.69/0.59  fof(f267,plain,(
% 1.69/0.59    m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.69/0.59    inference(subsumption_resolution,[],[f266,f109])).
% 1.69/0.59  fof(f266,plain,(
% 1.69/0.59    ~v1_funct_1(k2_funct_1(sK2)) | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.69/0.59    inference(subsumption_resolution,[],[f253,f188])).
% 1.69/0.59  fof(f253,plain,(
% 1.69/0.59    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.69/0.59    inference(resolution,[],[f197,f80])).
% 1.69/0.59  fof(f1013,plain,(
% 1.69/0.59    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_xboole_0)),
% 1.69/0.59    inference(backward_demodulation,[],[f733,f995])).
% 1.69/0.59  fof(f1020,plain,(
% 1.69/0.59    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    inference(backward_demodulation,[],[f742,f995])).
% 1.69/0.59  fof(f1356,plain,(
% 1.69/0.59    ~r2_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    inference(backward_demodulation,[],[f1293,f1351])).
% 1.69/0.59  fof(f1351,plain,(
% 1.69/0.59    k1_xboole_0 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0))),
% 1.69/0.59    inference(subsumption_resolution,[],[f1320,f1350])).
% 1.69/0.59  fof(f1350,plain,(
% 1.69/0.59    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.69/0.59    inference(backward_demodulation,[],[f1287,f1349])).
% 1.69/0.59  fof(f1349,plain,(
% 1.69/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    inference(subsumption_resolution,[],[f1330,f1288])).
% 1.69/0.59  fof(f1288,plain,(
% 1.69/0.59    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    inference(backward_demodulation,[],[f1008,f1284])).
% 1.69/0.59  fof(f1008,plain,(
% 1.69/0.59    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)),
% 1.69/0.59    inference(backward_demodulation,[],[f727,f995])).
% 1.69/0.59  fof(f1330,plain,(
% 1.69/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    inference(resolution,[],[f1289,f86])).
% 1.69/0.59  fof(f1289,plain,(
% 1.69/0.59    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.69/0.59    inference(backward_demodulation,[],[f1009,f1284])).
% 1.69/0.59  fof(f1009,plain,(
% 1.69/0.59    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 1.69/0.59    inference(backward_demodulation,[],[f728,f995])).
% 1.69/0.59  fof(f1287,plain,(
% 1.69/0.59    k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0)),
% 1.69/0.59    inference(backward_demodulation,[],[f1007,f1284])).
% 1.69/0.59  fof(f1007,plain,(
% 1.69/0.59    k1_relat_1(k1_xboole_0) = k1_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)),
% 1.69/0.59    inference(backward_demodulation,[],[f726,f995])).
% 1.69/0.59  fof(f1320,plain,(
% 1.69/0.59    k1_xboole_0 = k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.69/0.59    inference(forward_demodulation,[],[f1312,f1284])).
% 1.69/0.59  fof(f1312,plain,(
% 1.69/0.59    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))),
% 1.69/0.59    inference(backward_demodulation,[],[f1061,f1284])).
% 1.69/0.59  fof(f1061,plain,(
% 1.69/0.59    k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))),
% 1.69/0.59    inference(forward_demodulation,[],[f1019,f995])).
% 1.69/0.59  fof(f1019,plain,(
% 1.69/0.59    k2_struct_0(sK0) != k1_relat_1(k1_xboole_0) | sK2 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.59    inference(backward_demodulation,[],[f740,f995])).
% 1.69/0.59  fof(f1293,plain,(
% 1.69/0.59    ~r2_funct_2(k1_xboole_0,k1_xboole_0,k2_tops_2(k1_xboole_0,k1_xboole_0,k2_funct_1(k1_xboole_0)),k1_xboole_0)),
% 1.69/0.59    inference(backward_demodulation,[],[f1013,f1284])).
% 1.69/0.59  % SZS output end Proof for theBenchmark
% 1.69/0.59  % (7029)------------------------------
% 1.69/0.59  % (7029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (7029)Termination reason: Refutation
% 1.69/0.59  
% 1.69/0.59  % (7029)Memory used [KB]: 2174
% 1.69/0.59  % (7029)Time elapsed: 0.139 s
% 1.69/0.59  % (7029)------------------------------
% 1.69/0.59  % (7029)------------------------------
% 1.69/0.59  % (7009)Success in time 0.226 s
%------------------------------------------------------------------------------
