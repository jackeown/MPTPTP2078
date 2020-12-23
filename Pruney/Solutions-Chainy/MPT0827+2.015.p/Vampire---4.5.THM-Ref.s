%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 169 expanded)
%              Number of leaves         :   14 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  199 ( 523 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(global_subsumption,[],[f134,f189])).

fof(f189,plain,(
    ~ r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f149,f187])).

fof(f187,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f53,f33])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
      | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
    & r1_tarski(k6_relat_1(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
          | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
        & r1_tarski(k6_relat_1(X2),X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
        | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) )
      & r1_tarski(k6_relat_1(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X2,k2_relset_1(X0,X1,X3))
        | ~ r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      & r1_tarski(k6_relat_1(X2),X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(k6_relat_1(X2),X3)
         => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
            & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f149,plain,(
    ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f147,f148])).

fof(f148,plain,(
    r1_tarski(sK2,k1_relat_1(sK3)) ),
    inference(resolution,[],[f144,f34])).

fof(f34,plain,(
    r1_tarski(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f144,plain,(
    ! [X1] :
      ( ~ r1_tarski(k6_relat_1(X1),sK3)
      | r1_tarski(X1,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f142,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_relat_1(X0),X1)
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f70,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_relat_1(X0),X1)
      | r1_tarski(k1_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(resolution,[],[f41,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f142,plain,(
    ! [X0] :
      ( v4_relat_1(X0,k1_relat_1(sK3))
      | ~ r1_tarski(X0,sK3) ) ),
    inference(resolution,[],[f141,f82])).

fof(f82,plain,(
    v4_relat_1(sK3,k1_relat_1(sK3)) ),
    inference(resolution,[],[f79,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f79,plain,(
    ! [X5] :
      ( ~ r1_tarski(k1_relat_1(sK3),X5)
      | v4_relat_1(sK3,X5) ) ),
    inference(resolution,[],[f42,f62])).

fof(f62,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f59,f33])).

fof(f59,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | v1_relat_1(X2) ) ),
    inference(resolution,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(sK3,X0)
      | v4_relat_1(X1,X0)
      | ~ r1_tarski(X1,sK3) ) ),
    inference(resolution,[],[f140,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f140,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v4_relat_1(sK3,X8)
      | v4_relat_1(X7,X8) ) ),
    inference(resolution,[],[f46,f62])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v4_relat_1(X1,X0)
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

fof(f147,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK3))
    | ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(backward_demodulation,[],[f35,f145])).

fof(f145,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f52,f33])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f35,plain,
    ( ~ r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f134,plain,(
    r1_tarski(sK2,k2_relat_1(sK3)) ),
    inference(resolution,[],[f133,f34])).

fof(f133,plain,(
    ! [X1] :
      ( ~ r1_tarski(k6_relat_1(X1),sK3)
      | r1_tarski(X1,k2_relat_1(sK3)) ) ),
    inference(resolution,[],[f131,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(k6_relat_1(X0),X1)
      | r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f84,f38])).

fof(f38,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(k6_relat_1(X0),X1)
      | r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) ) ),
    inference(resolution,[],[f43,f36])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f131,plain,(
    ! [X0] :
      ( v5_relat_1(X0,k2_relat_1(sK3))
      | ~ r1_tarski(X0,sK3) ) ),
    inference(resolution,[],[f130,f96])).

fof(f96,plain,(
    v5_relat_1(sK3,k2_relat_1(sK3)) ),
    inference(resolution,[],[f93,f54])).

fof(f93,plain,(
    ! [X5] :
      ( ~ r1_tarski(k2_relat_1(sK3),X5)
      | v5_relat_1(sK3,X5) ) ),
    inference(resolution,[],[f44,f62])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(sK3,X0)
      | v5_relat_1(X1,X0)
      | ~ r1_tarski(X1,sK3) ) ),
    inference(resolution,[],[f129,f51])).

fof(f129,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(sK3))
      | ~ v5_relat_1(sK3,X8)
      | v5_relat_1(X7,X8) ) ),
    inference(resolution,[],[f45,f62])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | v5_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:51:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (5095)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (5088)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.48  % (5100)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (5088)Refutation not found, incomplete strategy% (5088)------------------------------
% 0.21/0.49  % (5088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5111)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (5113)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.49  % (5088)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (5088)Memory used [KB]: 10618
% 0.21/0.49  % (5088)Time elapsed: 0.080 s
% 0.21/0.49  % (5088)------------------------------
% 0.21/0.49  % (5088)------------------------------
% 0.21/0.49  % (5094)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (5100)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(global_subsumption,[],[f134,f189])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ~r1_tarski(sK2,k2_relat_1(sK3))),
% 0.21/0.49    inference(backward_demodulation,[],[f149,f187])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f53,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    (~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => ((~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))) & r1_tarski(k6_relat_1(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : (((~r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(X2,k1_relset_1(X0,X1,X3))) & r1_tarski(k6_relat_1(X2),X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.49    inference(subsumption_resolution,[],[f147,f148])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    r1_tarski(sK2,k1_relat_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f144,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    r1_tarski(k6_relat_1(sK2),sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(k6_relat_1(X1),sK3) | r1_tarski(X1,k1_relat_1(sK3))) )),
% 0.21/0.49    inference(resolution,[],[f142,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_relat_1(k6_relat_1(X0),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f70,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_relat_1(k6_relat_1(X0),X1) | r1_tarski(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 0.21/0.49    inference(resolution,[],[f41,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X0] : (v4_relat_1(X0,k1_relat_1(sK3)) | ~r1_tarski(X0,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f141,f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    v4_relat_1(sK3,k1_relat_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f79,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X5] : (~r1_tarski(k1_relat_1(sK3),X5) | v4_relat_1(sK3,X5)) )),
% 0.21/0.49    inference(resolution,[],[f42,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f59,f33])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(resolution,[],[f39,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_relat_1(sK3,X0) | v4_relat_1(X1,X0) | ~r1_tarski(X1,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f140,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v4_relat_1(sK3,X8) | v4_relat_1(X7,X8)) )),
% 0.21/0.49    inference(resolution,[],[f46,f62])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v4_relat_1(X1,X0) | v4_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~r1_tarski(sK2,k1_relat_1(sK3)) | ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.21/0.49    inference(backward_demodulation,[],[f35,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f52,f33])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~r1_tarski(sK2,k2_relset_1(sK0,sK1,sK3)) | ~r1_tarski(sK2,k1_relset_1(sK0,sK1,sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    r1_tarski(sK2,k2_relat_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f133,f34])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(k6_relat_1(X1),sK3) | r1_tarski(X1,k2_relat_1(sK3))) )),
% 0.21/0.49    inference(resolution,[],[f131,f87])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v5_relat_1(k6_relat_1(X0),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f84,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v5_relat_1(k6_relat_1(X0),X1) | r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)) )),
% 0.21/0.49    inference(resolution,[],[f43,f36])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ( ! [X0] : (v5_relat_1(X0,k2_relat_1(sK3)) | ~r1_tarski(X0,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f130,f96])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    v5_relat_1(sK3,k2_relat_1(sK3))),
% 0.21/0.49    inference(resolution,[],[f93,f54])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X5] : (~r1_tarski(k2_relat_1(sK3),X5) | v5_relat_1(sK3,X5)) )),
% 0.21/0.49    inference(resolution,[],[f44,f62])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v5_relat_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v5_relat_1(sK3,X0) | v5_relat_1(X1,X0) | ~r1_tarski(X1,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f129,f51])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(sK3)) | ~v5_relat_1(sK3,X8) | v5_relat_1(X7,X8)) )),
% 0.21/0.49    inference(resolution,[],[f45,f62])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | v5_relat_1(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (5100)------------------------------
% 0.21/0.49  % (5100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5100)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (5100)Memory used [KB]: 6268
% 0.21/0.49  % (5100)Time elapsed: 0.093 s
% 0.21/0.49  % (5100)------------------------------
% 0.21/0.49  % (5100)------------------------------
% 0.21/0.49  % (5101)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (5087)Success in time 0.131 s
%------------------------------------------------------------------------------
