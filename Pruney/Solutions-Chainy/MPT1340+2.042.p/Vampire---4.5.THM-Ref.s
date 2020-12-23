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
% DateTime   : Thu Dec  3 13:14:23 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 932 expanded)
%              Number of leaves         :    9 ( 184 expanded)
%              Depth                    :   16
%              Number of atoms          :  344 (5025 expanded)
%              Number of equality atoms :   69 ( 801 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(subsumption_resolution,[],[f163,f62])).

fof(f62,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f27,f59,f58,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_funct_2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f53,f50])).

fof(f50,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unit_resulting_resolution,[],[f34,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f34,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f29,f51])).

fof(f51,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f35,f36])).

fof(f35,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f52,f50])).

fof(f52,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f28,f51])).

fof(f28,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f163,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(backward_demodulation,[],[f71,f162])).

fof(f162,plain,(
    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f153,f61])).

fof(f61,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f31,f60,f27,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f60,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f58,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f31,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f153,plain,(
    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f111,f63,f64,f65,f145,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f145,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f142,f70])).

fof(f70,plain,(
    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(unit_resulting_resolution,[],[f31,f27,f59,f57,f58,f45])).

fof(f57,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f54,f50])).

fof(f54,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f30,f51])).

fof(f30,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f142,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f31,f59,f58,f57,f129])).

fof(f129,plain,(
    ! [X1] :
      ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_funct_1(X1)
      | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f127,f35])).

fof(f127,plain,(
    ! [X1] :
      ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ l1_struct_0(sK0)
      | ~ v2_funct_1(X1)
      | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) ) ),
    inference(superposition,[],[f102,f51])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X1)
      | k2_struct_0(X0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),k2_struct_0(sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f101,f34])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X1)
      | k2_struct_0(X0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),k2_struct_0(sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f97,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1)
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X1)
      | k2_struct_0(X0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),k2_struct_0(sK1),X1)) ) ),
    inference(superposition,[],[f39,f50])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f65,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f27,f31,f59,f57,f58,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f64,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f31,f27,f59,f57,f58,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f31,f59,f57,f58,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f111,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f108,f70])).

fof(f108,plain,(
    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f31,f59,f58,f57,f106])).

fof(f106,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_funct_1(X0)
      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f104,f34])).

fof(f104,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_funct_1(X0)
      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0)) ) ),
    inference(superposition,[],[f79,f50])).

fof(f79,plain,(
    ! [X2,X3] :
      ( k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X2),X3)
      | ~ l1_struct_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_struct_0(sK0),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X2))))
      | ~ v2_funct_1(X3)
      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X2),X3)) ) ),
    inference(subsumption_resolution,[],[f75,f35])).

fof(f75,plain,(
    ! [X2,X3] :
      ( k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X2),X3)
      | ~ l1_struct_0(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_struct_0(sK0),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X2))))
      | ~ l1_struct_0(sK0)
      | ~ v2_funct_1(X3)
      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X2),X3)) ) ),
    inference(superposition,[],[f37,f51])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

fof(f71,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(backward_demodulation,[],[f56,f70])).

fof(f56,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f55,f50])).

fof(f55,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f32,f51])).

fof(f32,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:00:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (17739)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (17757)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.56  % (17756)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.56  % (17745)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.56  % (17746)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.56  % (17741)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.56  % (17740)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.56  % (17737)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % (17738)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.53/0.56  % (17755)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.53/0.56  % (17741)Refutation found. Thanks to Tanya!
% 1.53/0.56  % SZS status Theorem for theBenchmark
% 1.53/0.56  % (17747)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.53/0.57  % (17736)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.53/0.57  % (17740)Refutation not found, incomplete strategy% (17740)------------------------------
% 1.53/0.57  % (17740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (17749)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.53/0.57  % (17745)Refutation not found, incomplete strategy% (17745)------------------------------
% 1.53/0.57  % (17745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (17753)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.53/0.58  % (17748)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.53/0.58  % (17747)Refutation not found, incomplete strategy% (17747)------------------------------
% 1.53/0.58  % (17747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (17747)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (17747)Memory used [KB]: 6268
% 1.53/0.58  % (17747)Time elapsed: 0.120 s
% 1.53/0.58  % (17747)------------------------------
% 1.53/0.58  % (17747)------------------------------
% 1.53/0.58  % (17754)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.53/0.58  % SZS output start Proof for theBenchmark
% 1.53/0.58  fof(f164,plain,(
% 1.53/0.58    $false),
% 1.53/0.58    inference(subsumption_resolution,[],[f163,f62])).
% 1.53/0.58  fof(f62,plain,(
% 1.53/0.58    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f27,f59,f58,f49])).
% 1.53/0.58  fof(f49,plain,(
% 1.53/0.58    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.53/0.58    inference(duplicate_literal_removal,[],[f48])).
% 1.53/0.58  fof(f48,plain,(
% 1.53/0.58    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.53/0.58    inference(equality_resolution,[],[f46])).
% 1.53/0.58  fof(f46,plain,(
% 1.53/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_funct_2(X0,X1,X2,X3)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f26])).
% 1.53/0.58  fof(f26,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.53/0.58    inference(flattening,[],[f25])).
% 1.53/0.58  fof(f25,plain,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.53/0.58    inference(ennf_transformation,[],[f3])).
% 1.53/0.58  fof(f3,axiom,(
% 1.53/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.53/0.58  fof(f58,plain,(
% 1.53/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.53/0.58    inference(backward_demodulation,[],[f53,f50])).
% 1.53/0.58  fof(f50,plain,(
% 1.53/0.58    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f34,f36])).
% 1.53/0.58  fof(f36,plain,(
% 1.53/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f13])).
% 1.53/0.58  fof(f13,plain,(
% 1.53/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f5])).
% 1.53/0.58  fof(f5,axiom,(
% 1.53/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    l1_struct_0(sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f12,plain,(
% 1.53/0.58    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.53/0.58    inference(flattening,[],[f11])).
% 1.53/0.58  fof(f11,plain,(
% 1.53/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f10])).
% 1.53/0.58  fof(f10,negated_conjecture,(
% 1.53/0.58    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.53/0.58    inference(negated_conjecture,[],[f9])).
% 1.53/0.58  fof(f9,conjecture,(
% 1.53/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 1.53/0.58  fof(f53,plain,(
% 1.53/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 1.53/0.58    inference(backward_demodulation,[],[f29,f51])).
% 1.53/0.58  fof(f51,plain,(
% 1.53/0.58    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f35,f36])).
% 1.53/0.58  fof(f35,plain,(
% 1.53/0.58    l1_struct_0(sK0)),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f29,plain,(
% 1.53/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f59,plain,(
% 1.53/0.58    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.53/0.58    inference(backward_demodulation,[],[f52,f50])).
% 1.53/0.58  fof(f52,plain,(
% 1.53/0.58    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.53/0.58    inference(backward_demodulation,[],[f28,f51])).
% 1.53/0.58  fof(f28,plain,(
% 1.53/0.58    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f27,plain,(
% 1.53/0.58    v1_funct_1(sK2)),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f163,plain,(
% 1.53/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 1.53/0.58    inference(backward_demodulation,[],[f71,f162])).
% 1.53/0.58  fof(f162,plain,(
% 1.53/0.58    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.53/0.58    inference(forward_demodulation,[],[f153,f61])).
% 1.53/0.58  fof(f61,plain,(
% 1.53/0.58    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f31,f60,f27,f40])).
% 1.53/0.58  fof(f40,plain,(
% 1.53/0.58    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 1.53/0.58    inference(cnf_transformation,[],[f19])).
% 1.53/0.58  fof(f19,plain,(
% 1.53/0.58    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(flattening,[],[f18])).
% 1.53/0.58  fof(f18,plain,(
% 1.53/0.58    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f1])).
% 1.53/0.58  fof(f1,axiom,(
% 1.53/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.53/0.58  fof(f60,plain,(
% 1.53/0.58    v1_relat_1(sK2)),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f58,f41])).
% 1.53/0.58  fof(f41,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f20])).
% 1.53/0.58  fof(f20,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f2])).
% 1.53/0.58  fof(f2,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.53/0.58  fof(f31,plain,(
% 1.53/0.58    v2_funct_1(sK2)),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f153,plain,(
% 1.53/0.58    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f111,f63,f64,f65,f145,f45])).
% 1.53/0.58  fof(f45,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f24])).
% 1.53/0.58  fof(f24,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.53/0.58    inference(flattening,[],[f23])).
% 1.53/0.58  fof(f23,plain,(
% 1.53/0.58    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.53/0.58    inference(ennf_transformation,[],[f6])).
% 1.53/0.58  fof(f6,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 1.53/0.58  fof(f145,plain,(
% 1.53/0.58    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.53/0.58    inference(forward_demodulation,[],[f142,f70])).
% 1.53/0.58  fof(f70,plain,(
% 1.53/0.58    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f31,f27,f59,f57,f58,f45])).
% 1.53/0.58  fof(f57,plain,(
% 1.53/0.58    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.53/0.58    inference(backward_demodulation,[],[f54,f50])).
% 1.53/0.58  fof(f54,plain,(
% 1.53/0.58    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.53/0.58    inference(backward_demodulation,[],[f30,f51])).
% 1.53/0.58  fof(f30,plain,(
% 1.53/0.58    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f142,plain,(
% 1.53/0.58    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f27,f31,f59,f58,f57,f129])).
% 1.53/0.58  fof(f129,plain,(
% 1.53/0.58    ( ! [X1] : (k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(X1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f127,f35])).
% 1.53/0.58  fof(f127,plain,(
% 1.53/0.58    ( ! [X1] : (k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(X1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))) )),
% 1.53/0.58    inference(superposition,[],[f102,f51])).
% 1.53/0.58  fof(f102,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X1) | k2_struct_0(X0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),k2_struct_0(sK1),X1))) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f101,f34])).
% 1.53/0.58  fof(f101,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1) | ~l1_struct_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X1) | k2_struct_0(X0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),k2_struct_0(sK1),X1))) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f97,f33])).
% 1.53/0.58  fof(f33,plain,(
% 1.53/0.58    ~v2_struct_0(sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f12])).
% 1.53/0.58  fof(f97,plain,(
% 1.53/0.58    ( ! [X0,X1] : (k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),k2_struct_0(sK1),X1) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(X0),k2_struct_0(sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),k2_struct_0(sK1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X1) | k2_struct_0(X0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),k2_struct_0(sK1),X1))) )),
% 1.53/0.58    inference(superposition,[],[f39,f50])).
% 1.53/0.58  fof(f39,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f17])).
% 1.53/0.58  fof(f17,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.53/0.58    inference(flattening,[],[f16])).
% 1.53/0.58  fof(f16,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f7])).
% 1.53/0.58  fof(f7,axiom,(
% 1.53/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 1.53/0.58  fof(f65,plain,(
% 1.53/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f27,f31,f59,f57,f58,f44])).
% 1.53/0.58  fof(f44,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f22])).
% 1.53/0.58  fof(f22,plain,(
% 1.53/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.53/0.58    inference(flattening,[],[f21])).
% 1.53/0.58  fof(f21,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.53/0.58    inference(ennf_transformation,[],[f4])).
% 1.53/0.58  fof(f4,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.53/0.58  fof(f64,plain,(
% 1.53/0.58    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f31,f27,f59,f57,f58,f43])).
% 1.53/0.58  fof(f43,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f22])).
% 1.53/0.58  fof(f63,plain,(
% 1.53/0.58    v1_funct_1(k2_funct_1(sK2))),
% 1.53/0.58    inference(unit_resulting_resolution,[],[f27,f31,f59,f57,f58,f42])).
% 1.53/0.58  fof(f42,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f22])).
% 1.53/0.58  fof(f111,plain,(
% 1.53/0.58    v2_funct_1(k2_funct_1(sK2))),
% 1.53/0.58    inference(forward_demodulation,[],[f108,f70])).
% 1.68/0.58  fof(f108,plain,(
% 1.68/0.58    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.68/0.58    inference(unit_resulting_resolution,[],[f27,f31,f59,f58,f57,f106])).
% 1.68/0.58  fof(f106,plain,(
% 1.68/0.58    ( ! [X0] : (k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(X0) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0))) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f104,f34])).
% 1.68/0.58  fof(f104,plain,(
% 1.68/0.58    ( ! [X0] : (k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0) | ~l1_struct_0(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(X0) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0))) )),
% 1.68/0.58    inference(superposition,[],[f79,f50])).
% 1.68/0.58  fof(f79,plain,(
% 1.68/0.58    ( ! [X2,X3] : (k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X2),X3) | ~l1_struct_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k2_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X2)))) | ~v2_funct_1(X3) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X2),X3))) )),
% 1.68/0.58    inference(subsumption_resolution,[],[f75,f35])).
% 1.68/0.58  fof(f75,plain,(
% 1.68/0.58    ( ! [X2,X3] : (k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X2),X3) | ~l1_struct_0(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k2_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X2)))) | ~l1_struct_0(sK0) | ~v2_funct_1(X3) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X2),X3))) )),
% 1.68/0.58    inference(superposition,[],[f37,f51])).
% 1.68/0.58  fof(f37,plain,(
% 1.68/0.58    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 1.68/0.58    inference(cnf_transformation,[],[f15])).
% 1.68/0.58  fof(f15,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.68/0.58    inference(flattening,[],[f14])).
% 1.68/0.58  fof(f14,plain,(
% 1.68/0.58    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.68/0.58    inference(ennf_transformation,[],[f8])).
% 1.68/0.58  fof(f8,axiom,(
% 1.68/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 1.68/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).
% 1.68/0.58  fof(f71,plain,(
% 1.68/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 1.68/0.58    inference(backward_demodulation,[],[f56,f70])).
% 1.68/0.58  fof(f56,plain,(
% 1.68/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.68/0.58    inference(backward_demodulation,[],[f55,f50])).
% 1.68/0.58  fof(f55,plain,(
% 1.68/0.58    ~r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.68/0.58    inference(backward_demodulation,[],[f32,f51])).
% 1.68/0.58  fof(f32,plain,(
% 1.68/0.58    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.68/0.58    inference(cnf_transformation,[],[f12])).
% 1.68/0.58  % SZS output end Proof for theBenchmark
% 1.68/0.58  % (17741)------------------------------
% 1.68/0.58  % (17741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (17741)Termination reason: Refutation
% 1.68/0.58  
% 1.68/0.58  % (17741)Memory used [KB]: 1791
% 1.68/0.58  % (17741)Time elapsed: 0.124 s
% 1.68/0.58  % (17741)------------------------------
% 1.68/0.58  % (17741)------------------------------
% 1.68/0.58  % (17740)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (17740)Memory used [KB]: 10746
% 1.68/0.58  % (17740)Time elapsed: 0.121 s
% 1.68/0.58  % (17740)------------------------------
% 1.68/0.58  % (17740)------------------------------
% 1.68/0.59  % (17733)Success in time 0.22 s
%------------------------------------------------------------------------------
