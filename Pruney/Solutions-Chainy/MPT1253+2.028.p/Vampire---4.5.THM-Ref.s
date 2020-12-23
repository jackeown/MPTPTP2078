%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:26 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 107 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  132 ( 376 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f565,plain,(
    $false ),
    inference(subsumption_resolution,[],[f563,f28])).

fof(f28,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,X1),X1)
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),X1)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f563,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f529,f378])).

fof(f378,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f377,f102])).

fof(f102,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f101,f25])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f101,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f97,f27])).

fof(f27,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f30,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f377,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))) ),
    inference(forward_demodulation,[],[f376,f41])).

fof(f41,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f33,f26])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f376,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f372,f25])).

fof(f372,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(f529,plain,(
    ! [X6,X7] : r1_tarski(k9_subset_1(u1_struct_0(sK0),X6,k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X7))),X6) ),
    inference(superposition,[],[f31,f511])).

fof(f511,plain,(
    ! [X0,X1] : k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X1)))) ),
    inference(resolution,[],[f433,f25])).

fof(f433,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X2))) = k4_xboole_0(X1,k4_xboole_0(X1,k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X2)))) ) ),
    inference(resolution,[],[f428,f31])).

fof(f428,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X3,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k4_xboole_0(X2,k4_xboole_0(X2,k2_pre_topc(X1,X3))) ) ),
    inference(resolution,[],[f50,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f50,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | k9_subset_1(u1_struct_0(X4),X5,k2_pre_topc(X4,X6)) = k4_xboole_0(X5,k4_xboole_0(X5,k2_pre_topc(X4,X6)))
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f38,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f37,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:04:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (800784385)
% 0.13/0.37  ipcrm: permission denied for id (801406978)
% 0.13/0.37  ipcrm: permission denied for id (800817155)
% 0.13/0.38  ipcrm: permission denied for id (800849924)
% 0.13/0.38  ipcrm: permission denied for id (801439749)
% 0.13/0.38  ipcrm: permission denied for id (801505287)
% 0.13/0.38  ipcrm: permission denied for id (801570825)
% 0.13/0.38  ipcrm: permission denied for id (805470218)
% 0.13/0.38  ipcrm: permission denied for id (805535756)
% 0.13/0.39  ipcrm: permission denied for id (805568525)
% 0.13/0.39  ipcrm: permission denied for id (800882702)
% 0.13/0.39  ipcrm: permission denied for id (805601295)
% 0.13/0.39  ipcrm: permission denied for id (801767440)
% 0.13/0.39  ipcrm: permission denied for id (800915473)
% 0.13/0.39  ipcrm: permission denied for id (801800210)
% 0.13/0.39  ipcrm: permission denied for id (801832979)
% 0.13/0.39  ipcrm: permission denied for id (801865748)
% 0.13/0.40  ipcrm: permission denied for id (805634069)
% 0.13/0.40  ipcrm: permission denied for id (805666838)
% 0.13/0.40  ipcrm: permission denied for id (801964055)
% 0.13/0.40  ipcrm: permission denied for id (801996824)
% 0.13/0.40  ipcrm: permission denied for id (802062362)
% 0.13/0.40  ipcrm: permission denied for id (800948251)
% 0.13/0.40  ipcrm: permission denied for id (805732380)
% 0.13/0.41  ipcrm: permission denied for id (802127901)
% 0.13/0.41  ipcrm: permission denied for id (802193439)
% 0.13/0.41  ipcrm: permission denied for id (802226208)
% 0.13/0.41  ipcrm: permission denied for id (805797921)
% 0.13/0.41  ipcrm: permission denied for id (802291746)
% 0.13/0.41  ipcrm: permission denied for id (801013795)
% 0.13/0.41  ipcrm: permission denied for id (802324516)
% 0.13/0.42  ipcrm: permission denied for id (802390054)
% 0.13/0.42  ipcrm: permission denied for id (802422823)
% 0.13/0.42  ipcrm: permission denied for id (802488361)
% 0.13/0.42  ipcrm: permission denied for id (802521130)
% 0.13/0.42  ipcrm: permission denied for id (805896235)
% 0.13/0.42  ipcrm: permission denied for id (805929004)
% 0.13/0.43  ipcrm: permission denied for id (806027311)
% 0.13/0.43  ipcrm: permission denied for id (806060080)
% 0.13/0.43  ipcrm: permission denied for id (806092849)
% 0.20/0.43  ipcrm: permission denied for id (806158387)
% 0.20/0.43  ipcrm: permission denied for id (802881589)
% 0.20/0.43  ipcrm: permission denied for id (802914358)
% 0.20/0.44  ipcrm: permission denied for id (802947127)
% 0.20/0.44  ipcrm: permission denied for id (802979896)
% 0.20/0.44  ipcrm: permission denied for id (803012665)
% 0.20/0.44  ipcrm: permission denied for id (806289468)
% 0.20/0.44  ipcrm: permission denied for id (801079358)
% 0.20/0.45  ipcrm: permission denied for id (803209279)
% 0.20/0.45  ipcrm: permission denied for id (806355008)
% 0.20/0.45  ipcrm: permission denied for id (803274817)
% 0.20/0.45  ipcrm: permission denied for id (806387778)
% 0.20/0.45  ipcrm: permission denied for id (803340355)
% 0.20/0.45  ipcrm: permission denied for id (806420548)
% 0.20/0.45  ipcrm: permission denied for id (806486086)
% 0.20/0.45  ipcrm: permission denied for id (806518855)
% 0.20/0.46  ipcrm: permission denied for id (803536969)
% 0.20/0.46  ipcrm: permission denied for id (806584394)
% 0.20/0.46  ipcrm: permission denied for id (803602507)
% 0.20/0.46  ipcrm: permission denied for id (806617164)
% 0.20/0.46  ipcrm: permission denied for id (803668045)
% 0.20/0.47  ipcrm: permission denied for id (806715472)
% 0.20/0.47  ipcrm: permission denied for id (806748241)
% 0.20/0.47  ipcrm: permission denied for id (803831890)
% 0.20/0.47  ipcrm: permission denied for id (801177684)
% 0.20/0.47  ipcrm: permission denied for id (803897429)
% 0.20/0.47  ipcrm: permission denied for id (806813782)
% 0.20/0.47  ipcrm: permission denied for id (806846551)
% 0.20/0.48  ipcrm: permission denied for id (803995736)
% 0.20/0.48  ipcrm: permission denied for id (804061274)
% 0.20/0.48  ipcrm: permission denied for id (804094043)
% 0.20/0.48  ipcrm: permission denied for id (806912092)
% 0.20/0.48  ipcrm: permission denied for id (804159581)
% 0.20/0.48  ipcrm: permission denied for id (804225119)
% 0.20/0.48  ipcrm: permission denied for id (804257888)
% 0.20/0.49  ipcrm: permission denied for id (806977633)
% 0.20/0.49  ipcrm: permission denied for id (804356195)
% 0.20/0.49  ipcrm: permission denied for id (807043172)
% 0.20/0.49  ipcrm: permission denied for id (804421733)
% 0.20/0.49  ipcrm: permission denied for id (804454502)
% 0.20/0.49  ipcrm: permission denied for id (804487271)
% 0.20/0.49  ipcrm: permission denied for id (807075944)
% 0.20/0.50  ipcrm: permission denied for id (804552809)
% 0.20/0.50  ipcrm: permission denied for id (807141483)
% 0.20/0.50  ipcrm: permission denied for id (804683884)
% 0.20/0.50  ipcrm: permission denied for id (807174253)
% 0.20/0.50  ipcrm: permission denied for id (807207022)
% 0.20/0.50  ipcrm: permission denied for id (804782191)
% 0.20/0.50  ipcrm: permission denied for id (804814960)
% 0.20/0.51  ipcrm: permission denied for id (807272562)
% 0.20/0.51  ipcrm: permission denied for id (804913267)
% 0.20/0.51  ipcrm: permission denied for id (804946036)
% 0.20/0.51  ipcrm: permission denied for id (805044342)
% 0.20/0.51  ipcrm: permission denied for id (805077111)
% 0.20/0.51  ipcrm: permission denied for id (807338104)
% 0.20/0.51  ipcrm: permission denied for id (807370873)
% 0.20/0.52  ipcrm: permission denied for id (807403642)
% 0.20/0.52  ipcrm: permission denied for id (805208187)
% 0.20/0.52  ipcrm: permission denied for id (805273725)
% 0.20/0.52  ipcrm: permission denied for id (807534719)
% 0.55/0.59  % (28630)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.55/0.59  % (28630)Refutation not found, incomplete strategy% (28630)------------------------------
% 0.55/0.59  % (28630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.55/0.59  % (28630)Termination reason: Refutation not found, incomplete strategy
% 0.55/0.59  
% 0.55/0.59  % (28630)Memory used [KB]: 10618
% 0.55/0.59  % (28630)Time elapsed: 0.004 s
% 0.55/0.59  % (28630)------------------------------
% 0.55/0.59  % (28630)------------------------------
% 0.85/0.61  % (28628)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.85/0.62  % (28636)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.85/0.63  % (28626)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.85/0.63  % (28624)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.85/0.63  % (28623)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.85/0.63  % (28628)Refutation found. Thanks to Tanya!
% 0.85/0.63  % SZS status Theorem for theBenchmark
% 0.85/0.63  % SZS output start Proof for theBenchmark
% 0.85/0.63  fof(f565,plain,(
% 0.85/0.63    $false),
% 0.85/0.63    inference(subsumption_resolution,[],[f563,f28])).
% 0.85/0.63  fof(f28,plain,(
% 0.85/0.63    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.85/0.63    inference(cnf_transformation,[],[f23])).
% 0.85/0.63  fof(f23,plain,(
% 0.85/0.63    (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.85/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f22,f21])).
% 0.85/0.64  fof(f21,plain,(
% 0.85/0.64    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.85/0.64    introduced(choice_axiom,[])).
% 0.85/0.64  fof(f22,plain,(
% 0.85/0.64    ? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),X1) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,sK1),sK1) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.85/0.64    introduced(choice_axiom,[])).
% 0.85/0.64  fof(f13,plain,(
% 0.85/0.64    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.85/0.64    inference(flattening,[],[f12])).
% 0.85/0.64  fof(f12,plain,(
% 0.85/0.64    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.85/0.64    inference(ennf_transformation,[],[f10])).
% 0.85/0.64  fof(f10,negated_conjecture,(
% 0.85/0.64    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.85/0.64    inference(negated_conjecture,[],[f9])).
% 0.85/0.64  fof(f9,conjecture,(
% 0.85/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 0.85/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 0.85/0.64  fof(f563,plain,(
% 0.85/0.64    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.85/0.64    inference(superposition,[],[f529,f378])).
% 0.85/0.64  fof(f378,plain,(
% 0.85/0.64    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 0.85/0.64    inference(forward_demodulation,[],[f377,f102])).
% 0.85/0.64  fof(f102,plain,(
% 0.85/0.64    sK1 = k2_pre_topc(sK0,sK1)),
% 0.85/0.64    inference(subsumption_resolution,[],[f101,f25])).
% 0.85/0.64  fof(f25,plain,(
% 0.85/0.64    l1_pre_topc(sK0)),
% 0.85/0.64    inference(cnf_transformation,[],[f23])).
% 0.85/0.64  fof(f101,plain,(
% 0.85/0.64    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.85/0.64    inference(subsumption_resolution,[],[f97,f27])).
% 0.85/0.64  fof(f27,plain,(
% 0.85/0.64    v4_pre_topc(sK1,sK0)),
% 0.85/0.64    inference(cnf_transformation,[],[f23])).
% 0.85/0.64  fof(f97,plain,(
% 0.85/0.64    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.85/0.64    inference(resolution,[],[f30,f26])).
% 0.85/0.64  fof(f26,plain,(
% 0.85/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.85/0.64    inference(cnf_transformation,[],[f23])).
% 0.85/0.64  fof(f30,plain,(
% 0.85/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.85/0.64    inference(cnf_transformation,[],[f16])).
% 0.85/0.64  fof(f16,plain,(
% 0.85/0.64    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.85/0.64    inference(flattening,[],[f15])).
% 0.85/0.64  fof(f15,plain,(
% 0.85/0.64    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.85/0.64    inference(ennf_transformation,[],[f11])).
% 0.85/0.64  fof(f11,plain,(
% 0.85/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 0.85/0.64    inference(pure_predicate_removal,[],[f7])).
% 0.85/0.64  fof(f7,axiom,(
% 0.85/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.85/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.85/0.64  fof(f377,plain,(
% 0.85/0.64    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))),
% 0.85/0.64    inference(forward_demodulation,[],[f376,f41])).
% 0.85/0.64  fof(f41,plain,(
% 0.85/0.64    k4_xboole_0(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK1)),
% 0.85/0.64    inference(resolution,[],[f33,f26])).
% 0.85/0.64  fof(f33,plain,(
% 0.85/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.85/0.64    inference(cnf_transformation,[],[f17])).
% 0.85/0.64  fof(f17,plain,(
% 0.85/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.85/0.64    inference(ennf_transformation,[],[f3])).
% 0.85/0.64  fof(f3,axiom,(
% 0.85/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.85/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.85/0.64  fof(f376,plain,(
% 0.85/0.64    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.85/0.64    inference(subsumption_resolution,[],[f372,f25])).
% 0.85/0.64  fof(f372,plain,(
% 0.85/0.64    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0)),
% 0.85/0.64    inference(resolution,[],[f29,f26])).
% 0.85/0.64  fof(f29,plain,(
% 0.85/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 0.85/0.64    inference(cnf_transformation,[],[f14])).
% 0.85/0.64  fof(f14,plain,(
% 0.85/0.64    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.85/0.64    inference(ennf_transformation,[],[f8])).
% 0.85/0.64  fof(f8,axiom,(
% 0.85/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.85/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).
% 0.85/0.64  fof(f529,plain,(
% 0.85/0.64    ( ! [X6,X7] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X6,k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X7))),X6)) )),
% 0.85/0.64    inference(superposition,[],[f31,f511])).
% 0.85/0.64  fof(f511,plain,(
% 0.85/0.64    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X1))) = k4_xboole_0(X0,k4_xboole_0(X0,k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),X1))))) )),
% 0.85/0.64    inference(resolution,[],[f433,f25])).
% 0.85/0.64  fof(f433,plain,(
% 0.85/0.64    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X2))) = k4_xboole_0(X1,k4_xboole_0(X1,k2_pre_topc(X0,k4_xboole_0(u1_struct_0(X0),X2))))) )),
% 0.85/0.64    inference(resolution,[],[f428,f31])).
% 0.85/0.64  fof(f428,plain,(
% 0.85/0.64    ( ! [X2,X3,X1] : (~r1_tarski(X3,u1_struct_0(X1)) | ~l1_pre_topc(X1) | k9_subset_1(u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k4_xboole_0(X2,k4_xboole_0(X2,k2_pre_topc(X1,X3)))) )),
% 0.85/0.64    inference(resolution,[],[f50,f36])).
% 0.85/0.64  fof(f36,plain,(
% 0.85/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.85/0.64    inference(cnf_transformation,[],[f24])).
% 0.85/0.64  fof(f24,plain,(
% 0.85/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.85/0.64    inference(nnf_transformation,[],[f5])).
% 0.85/0.64  fof(f5,axiom,(
% 0.85/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.85/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.85/0.64  fof(f50,plain,(
% 0.85/0.64    ( ! [X6,X4,X5] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | k9_subset_1(u1_struct_0(X4),X5,k2_pre_topc(X4,X6)) = k4_xboole_0(X5,k4_xboole_0(X5,k2_pre_topc(X4,X6))) | ~l1_pre_topc(X4)) )),
% 0.85/0.64    inference(resolution,[],[f38,f34])).
% 0.85/0.64  fof(f34,plain,(
% 0.85/0.64    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.85/0.64    inference(cnf_transformation,[],[f19])).
% 0.85/0.64  fof(f19,plain,(
% 0.85/0.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.85/0.64    inference(flattening,[],[f18])).
% 0.85/0.64  fof(f18,plain,(
% 0.85/0.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.85/0.64    inference(ennf_transformation,[],[f6])).
% 0.85/0.64  fof(f6,axiom,(
% 0.85/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.85/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.85/0.64  fof(f38,plain,(
% 0.85/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.85/0.64    inference(definition_unfolding,[],[f37,f32])).
% 0.85/0.64  fof(f32,plain,(
% 0.85/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.85/0.64    inference(cnf_transformation,[],[f2])).
% 0.85/0.64  fof(f2,axiom,(
% 0.85/0.64    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.85/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.85/0.64  fof(f37,plain,(
% 0.85/0.64    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.85/0.64    inference(cnf_transformation,[],[f20])).
% 0.85/0.64  fof(f20,plain,(
% 0.85/0.64    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.85/0.64    inference(ennf_transformation,[],[f4])).
% 0.85/0.64  fof(f4,axiom,(
% 0.85/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.85/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.85/0.64  fof(f31,plain,(
% 0.85/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.85/0.64    inference(cnf_transformation,[],[f1])).
% 0.85/0.64  fof(f1,axiom,(
% 0.85/0.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.85/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.85/0.64  % SZS output end Proof for theBenchmark
% 0.85/0.64  % (28628)------------------------------
% 0.85/0.64  % (28628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.85/0.64  % (28628)Termination reason: Refutation
% 0.85/0.64  
% 0.85/0.64  % (28628)Memory used [KB]: 11513
% 0.85/0.64  % (28628)Time elapsed: 0.059 s
% 0.85/0.64  % (28628)------------------------------
% 0.85/0.64  % (28628)------------------------------
% 0.85/0.64  % (28632)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.85/0.64  % (28483)Success in time 0.273 s
%------------------------------------------------------------------------------
