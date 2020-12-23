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
% DateTime   : Thu Dec  3 13:07:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 131 expanded)
%              Number of leaves         :    5 (  24 expanded)
%              Depth                    :   17
%              Number of atoms          :  162 ( 637 expanded)
%              Number of equality atoms :   27 ( 156 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f41,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f20,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
          & ! [X4] : k1_tarski(X4) != X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
                & ! [X4] : k1_tarski(X4) != X1 )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3)
              & ! [X4] : k1_tarski(X4) != X1 )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_2)).

fof(f71,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(backward_demodulation,[],[f18,f68])).

fof(f68,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f67,f66])).

fof(f66,plain,(
    r1_tarski(sK3,sK2) ),
    inference(subsumption_resolution,[],[f65,f15])).

fof(f15,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f65,plain,
    ( r1_tarski(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f60,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_relset_1(X0,X1,X2,X3)
      | r1_tarski(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_relset_1)).

fof(f60,plain,(
    r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(subsumption_resolution,[],[f59,f31])).

fof(f31,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f59,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(forward_demodulation,[],[f58,f17])).

fof(f17,plain,(
    k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    | r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(subsumption_resolution,[],[f56,f14])).

fof(f14,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    | r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(resolution,[],[f43,f15])).

fof(f43,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1))
      | r1_relset_1(sK0,sK1,X1,sK2) ) ),
    inference(subsumption_resolution,[],[f42,f16])).

fof(f16,plain,(
    ! [X4] : k1_tarski(X4) != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1))
      | sK1 = k1_tarski(sK4(sK1))
      | r1_relset_1(sK0,sK1,X1,sK2) ) ),
    inference(subsumption_resolution,[],[f40,f19])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1))
      | sK1 = k1_tarski(sK4(sK1))
      | r1_relset_1(sK0,sK1,X1,sK2) ) ),
    inference(resolution,[],[f20,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
      | k1_tarski(sK4(X1)) = X1
      | r1_relset_1(X0,X1,X3,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_relset_1(X0,X1,X3,X2)
          | ? [X4] : k1_tarski(X4) = X1
          | ~ r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

% (1969)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( ! [X4] : k1_tarski(X4) != X1
              & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) )
           => r1_relset_1(X0,X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_2)).

fof(f67,plain,
    ( ~ r1_tarski(sK3,sK2)
    | sK2 = sK3 ),
    inference(resolution,[],[f64,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f64,plain,(
    r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f63,f20])).

fof(f63,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f54,f28])).

fof(f54,plain,(
    r1_relset_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f53,f31])).

fof(f53,plain,
    ( ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | r1_relset_1(sK0,sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f49,f19])).

fof(f49,plain,
    ( ~ v1_funct_1(sK2)
    | ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | r1_relset_1(sK0,sK1,sK2,sK3) ),
    inference(resolution,[],[f38,f20])).

fof(f38,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1))
      | r1_relset_1(sK0,sK1,X1,sK3) ) ),
    inference(forward_demodulation,[],[f37,f17])).

% (1978)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f37,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_tarski(k5_partfun1(sK0,sK1,sK3),k5_partfun1(sK0,sK1,X1))
      | r1_relset_1(sK0,sK1,X1,sK3) ) ),
    inference(subsumption_resolution,[],[f36,f16])).

fof(f36,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_tarski(k5_partfun1(sK0,sK1,sK3),k5_partfun1(sK0,sK1,X1))
      | sK1 = k1_tarski(sK4(sK1))
      | r1_relset_1(sK0,sK1,X1,sK3) ) ),
    inference(subsumption_resolution,[],[f34,f14])).

fof(f34,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r1_tarski(k5_partfun1(sK0,sK1,sK3),k5_partfun1(sK0,sK1,X1))
      | sK1 = k1_tarski(sK4(sK1))
      | r1_relset_1(sK0,sK1,X1,sK3) ) ),
    inference(resolution,[],[f15,f23])).

fof(f18,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:16:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (1974)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (1974)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f71,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.49    inference(resolution,[],[f20,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.49    inference(equality_resolution,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3) & ! [X4] : k1_tarski(X4) != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & (k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3) & ! [X4] : k1_tarski(X4) != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3) & ! [X4] : k1_tarski(X4) != X1) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.49    inference(negated_conjecture,[],[f5])).
% 0.21/0.49  fof(f5,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((k5_partfun1(X0,X1,X2) = k5_partfun1(X0,X1,X3) & ! [X4] : k1_tarski(X4) != X1) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_funct_2)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.49    inference(backward_demodulation,[],[f18,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    sK2 = sK3),
% 0.21/0.49    inference(subsumption_resolution,[],[f67,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    r1_tarski(sK3,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f65,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    r1_tarski(sK3,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(resolution,[],[f60,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_relset_1(X0,X1,X2,X3) | r1_tarski(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((r1_relset_1(X0,X1,X2,X3) <=> r1_tarski(X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_relset_1(X0,X1,X2,X3) <=> r1_tarski(X2,X3)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_relset_1)).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    r1_relset_1(sK0,sK1,sK3,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f59,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2)) | r1_relset_1(sK0,sK1,sK3,sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f58,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    k5_partfun1(sK0,sK1,sK2) = k5_partfun1(sK0,sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) | r1_relset_1(sK0,sK1,sK3,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f56,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ~v1_funct_1(sK3) | ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) | r1_relset_1(sK0,sK1,sK3,sK2)),
% 0.21/0.49    inference(resolution,[],[f43,f15])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1) | ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1)) | r1_relset_1(sK0,sK1,X1,sK2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f42,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X4] : (k1_tarski(X4) != sK1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1)) | sK1 = k1_tarski(sK4(sK1)) | r1_relset_1(sK0,sK1,X1,sK2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f40,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    v1_funct_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(sK2) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1)) | sK1 = k1_tarski(sK4(sK1)) | r1_relset_1(sK0,sK1,X1,sK2)) )),
% 0.21/0.49    inference(resolution,[],[f20,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) | k1_tarski(sK4(X1)) = X1 | r1_relset_1(X0,X1,X3,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (r1_relset_1(X0,X1,X3,X2) | ? [X4] : k1_tarski(X4) = X1 | ~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : ((r1_relset_1(X0,X1,X3,X2) | (? [X4] : k1_tarski(X4) = X1 | ~r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3)))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  % (1969)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((! [X4] : k1_tarski(X4) != X1 & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))) => r1_relset_1(X0,X1,X3,X2))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_funct_2)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~r1_tarski(sK3,sK2) | sK2 = sK3),
% 0.21/0.49    inference(resolution,[],[f64,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    r1_tarski(sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f63,f20])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    r1_tarski(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(resolution,[],[f54,f28])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    r1_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f53,f31])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2)) | r1_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f49,f19])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ~v1_funct_1(sK2) | ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2)) | r1_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.49    inference(resolution,[],[f38,f20])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X1) | ~r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X1)) | r1_relset_1(sK0,sK1,X1,sK3)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f37,f17])).
% 0.21/0.49  % (1978)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_tarski(k5_partfun1(sK0,sK1,sK3),k5_partfun1(sK0,sK1,X1)) | r1_relset_1(sK0,sK1,X1,sK3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f36,f16])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_tarski(k5_partfun1(sK0,sK1,sK3),k5_partfun1(sK0,sK1,X1)) | sK1 = k1_tarski(sK4(sK1)) | r1_relset_1(sK0,sK1,X1,sK3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f34,f14])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X1] : (~v1_funct_1(sK3) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r1_tarski(k5_partfun1(sK0,sK1,sK3),k5_partfun1(sK0,sK1,X1)) | sK1 = k1_tarski(sK4(sK1)) | r1_relset_1(sK0,sK1,X1,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f15,f23])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1974)------------------------------
% 0.21/0.49  % (1974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1974)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1974)Memory used [KB]: 6140
% 0.21/0.49  % (1974)Time elapsed: 0.076 s
% 0.21/0.49  % (1974)------------------------------
% 0.21/0.49  % (1974)------------------------------
% 0.21/0.50  % (1968)Success in time 0.131 s
%------------------------------------------------------------------------------
