%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 644 expanded)
%              Number of leaves         :    3 ( 122 expanded)
%              Depth                    :   18
%              Number of atoms          :  112 (2995 expanded)
%              Number of equality atoms :   51 (1205 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f42])).

fof(f42,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f38,f41])).

fof(f41,plain,(
    k1_xboole_0 = k2_struct_0(sK0) ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(superposition,[],[f10,f35])).

fof(f35,plain,(
    k1_xboole_0 = k2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f34,f28])).

fof(f28,plain,(
    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f26,f27])).

fof(f27,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f16,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f26,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f14,f23])).

fof(f23,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f15,f17])).

fof(f15,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f33,f30])).

fof(f30,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f24,f27])).

fof(f24,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f12,f23])).

fof(f12,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f32,f11])).

fof(f11,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f32,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(resolution,[],[f29,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k8_relset_1(X0,X1,X2,X1) = X0
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k8_relset_1(X0,X1,X2,X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f25,f27])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f13,f23])).

fof(f13,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f28,f35])).

fof(f57,plain,(
    k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f56,f44])).

fof(f44,plain,(
    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f36,f41])).

fof(f36,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f30,f35])).

fof(f56,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f53,f11])).

fof(f53,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    inference(resolution,[],[f43,f20])).

fof(f20,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k8_relset_1(X0,X1,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f37,f41])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    inference(backward_demodulation,[],[f29,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:09:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (25143)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (25143)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f57,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.47    inference(backward_demodulation,[],[f38,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.47    inference(superposition,[],[f10,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    k1_xboole_0 = k2_struct_0(sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f34,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.47    inference(backward_demodulation,[],[f26,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f16,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    l1_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f5])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.47    inference(backward_demodulation,[],[f14,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.21/0.47    inference(resolution,[],[f15,f17])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    l1_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f33,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.47    inference(backward_demodulation,[],[f24,f27])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.47    inference(backward_demodulation,[],[f12,f23])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f32,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.47    inference(resolution,[],[f29,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = X0 | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k8_relset_1(X0,X1,X2,X1) = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.47    inference(backward_demodulation,[],[f25,f27])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.47    inference(backward_demodulation,[],[f13,f23])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.47    inference(backward_demodulation,[],[f28,f35])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.21/0.47    inference(backward_demodulation,[],[f36,f41])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)),
% 0.21/0.47    inference(backward_demodulation,[],[f30,f35])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f53,f11])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.47    inference(resolution,[],[f43,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k8_relset_1(k1_xboole_0,X1,X2,X1)) )),
% 0.21/0.47    inference(equality_resolution,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k8_relset_1(X0,X1,X2,X1) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.21/0.47    inference(backward_demodulation,[],[f37,f41])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 0.21/0.47    inference(backward_demodulation,[],[f29,f35])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (25143)------------------------------
% 0.21/0.47  % (25143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25143)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (25143)Memory used [KB]: 1663
% 0.21/0.47  % (25143)Time elapsed: 0.006 s
% 0.21/0.47  % (25143)------------------------------
% 0.21/0.47  % (25143)------------------------------
% 0.21/0.47  % (25129)Success in time 0.113 s
%------------------------------------------------------------------------------
