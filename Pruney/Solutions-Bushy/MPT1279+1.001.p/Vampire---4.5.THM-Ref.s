%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1279+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:37 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 600 expanded)
%              Number of leaves         :    7 ( 130 expanded)
%              Depth                    :   17
%              Number of atoms          :  154 (1621 expanded)
%              Number of equality atoms :   44 ( 189 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f588,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f587])).

fof(f587,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(backward_demodulation,[],[f553,f560])).

fof(f560,plain,(
    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f555,f553])).

fof(f555,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f544,f53])).

fof(f53,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f44,f23])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v6_tops_1(X1,X0)
          <~> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v6_tops_1(X1,X0)
            <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_tops_1)).

fof(f44,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ v6_tops_1(sK1,sK0) ),
    inference(resolution,[],[f22,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_tops_1)).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f544,plain,
    ( v6_tops_1(sK1,sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(backward_demodulation,[],[f58,f543])).

fof(f543,plain,(
    k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f536,f288])).

fof(f288,plain,(
    m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f108,f38])).

fof(f38,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X5),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f23,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f108,plain,(
    m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f69,f106])).

fof(f106,plain,(
    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) ),
    inference(forward_demodulation,[],[f105,f48])).

fof(f48,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f105,plain,(
    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(subsumption_resolution,[],[f96,f23])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f47,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f69,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f54,f27])).

fof(f54,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f45,f23])).

fof(f45,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f22,f31])).

fof(f536,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) = k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f26,f109])).

fof(f109,plain,(
    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) ),
    inference(backward_demodulation,[],[f73,f106])).

fof(f73,plain,(
    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f64,f23])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) ),
    inference(resolution,[],[f54,f28])).

fof(f58,plain,
    ( v6_tops_1(sK1,sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f57,f47])).

fof(f57,plain,
    ( v6_tops_1(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f56,f23])).

fof(f56,plain,
    ( v6_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f20,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f20,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f553,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f545,f540])).

fof(f540,plain,(
    ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f539,f61])).

fof(f61,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | sK1 != k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f60,f22])).

fof(f60,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 != k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f59,f23])).

fof(f59,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 != k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f21,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f21,plain,
    ( ~ v6_tops_1(sK1,sK0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f539,plain,
    ( sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f538,f48])).

fof(f538,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f537,f47])).

fof(f537,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f531,f23])).

fof(f531,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f109,f25])).

fof(f545,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(backward_demodulation,[],[f103,f543])).

fof(f103,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f94,f23])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(resolution,[],[f47,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
