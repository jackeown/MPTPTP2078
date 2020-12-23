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
% DateTime   : Thu Dec  3 13:11:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 145 expanded)
%              Number of leaves         :    9 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 ( 527 expanded)
%              Number of equality atoms :   46 ( 136 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(global_subsumption,[],[f25,f23,f106])).

fof(f106,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f105,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f105,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f104,f65])).

fof(f65,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) ),
    inference(global_subsumption,[],[f23,f62])).

fof(f62,plain,(
    ! [X0] :
      ( k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f48,f24])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1)))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).

fof(f48,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | k7_subset_1(u1_struct_0(X1),k2_tops_1(X1,k2_tops_1(X1,X2)),X3) = k4_xboole_0(k2_tops_1(X1,k2_tops_1(X1,X2)),X3)
      | ~ l1_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | k7_subset_1(u1_struct_0(X1),k2_tops_1(X1,k2_tops_1(X1,X2)),X3) = k4_xboole_0(k2_tops_1(X1,k2_tops_1(X1,X2)),X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k7_subset_1(u1_struct_0(X1),k2_tops_1(X1,X0),X2) = k4_xboole_0(k2_tops_1(X1,X0),X2) ) ),
    inference(resolution,[],[f30,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f104,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f103,f57])).

fof(f57,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f23,f22,f54])).

fof(f54,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f40,f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_pre_topc(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_pre_topc(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f29,f30])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l79_tops_1)).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f100,f37])).

fof(f37,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(global_subsumption,[],[f23,f22,f34])).

fof(f34,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f28,f24])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).

fof(f100,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f24])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k2_tops_1(X0,k2_tops_1(X0,X1))),k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k2_tops_1(X0,k2_tops_1(X0,X1))),k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f44,f30])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,k2_tops_1(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k2_tops_1(X0,X1)),k1_tops_1(X0,k2_tops_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,k2_tops_1(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k2_tops_1(X0,X1)),k1_tops_1(X0,k2_tops_1(X0,X1)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f27,f30])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f25,plain,(
    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:38:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (17198)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.43  % (17193)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (17190)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.43  % (17200)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.43  % (17193)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(global_subsumption,[],[f25,f23,f106])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.43    inference(forward_demodulation,[],[f105,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | ~l1_pre_topc(sK0)),
% 0.21/0.43    inference(forward_demodulation,[],[f104,f65])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0)) )),
% 0.21/0.43    inference(global_subsumption,[],[f23,f62])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) = k4_xboole_0(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),X0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.43    inference(resolution,[],[f48,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f20,f19])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ? [X1] : (k2_tops_1(sK0,k2_tops_1(sK0,X1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.43    inference(flattening,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) != k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_tops_1)).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | k7_subset_1(u1_struct_0(X1),k2_tops_1(X1,k2_tops_1(X1,X2)),X3) = k4_xboole_0(k2_tops_1(X1,k2_tops_1(X1,X2)),X3) | ~l1_pre_topc(X1)) )),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f47])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X2,X3,X1] : (~l1_pre_topc(X1) | k7_subset_1(u1_struct_0(X1),k2_tops_1(X1,k2_tops_1(X1,X2)),X3) = k4_xboole_0(k2_tops_1(X1,k2_tops_1(X1,X2)),X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 0.21/0.43    inference(resolution,[],[f33,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(flattening,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k7_subset_1(u1_struct_0(X1),k2_tops_1(X1,X0),X2) = k4_xboole_0(k2_tops_1(X1,X0),X2)) )),
% 0.21/0.43    inference(resolution,[],[f30,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_xboole_0) | ~l1_pre_topc(sK0)),
% 0.21/0.43    inference(forward_demodulation,[],[f103,f57])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.44    inference(global_subsumption,[],[f23,f22,f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | k2_tops_1(sK0,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.44    inference(resolution,[],[f40,f24])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_pre_topc(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) = k2_pre_topc(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(resolution,[],[f29,f30])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_pre_topc(X0,k2_tops_1(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l79_tops_1)).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    v2_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_xboole_0) | ~l1_pre_topc(sK0)),
% 0.21/0.44    inference(forward_demodulation,[],[f100,f37])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.44    inference(global_subsumption,[],[f23,f22,f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    k1_xboole_0 = k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.44    inference(resolution,[],[f28,f24])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.44    inference(flattening,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_xboole_0 = k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l80_tops_1)).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1))),k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))) | ~l1_pre_topc(sK0)),
% 0.21/0.44    inference(resolution,[],[f72,f24])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k2_tops_1(X0,k2_tops_1(X0,X1))),k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | k2_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k2_tops_1(X0,k2_tops_1(X0,X1))),k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(resolution,[],[f44,f30])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,k2_tops_1(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k2_tops_1(X0,X1)),k1_tops_1(X0,k2_tops_1(X0,X1)))) )),
% 0.21/0.44    inference(duplicate_literal_removal,[],[f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_tops_1(X0,k2_tops_1(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k2_tops_1(X0,X1)),k1_tops_1(X0,k2_tops_1(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(resolution,[],[f27,f30])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    l1_pre_topc(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    k2_tops_1(sK0,k2_tops_1(sK0,sK1)) != k2_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (17193)------------------------------
% 0.21/0.44  % (17193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (17193)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (17193)Memory used [KB]: 6140
% 0.21/0.44  % (17193)Time elapsed: 0.008 s
% 0.21/0.44  % (17193)------------------------------
% 0.21/0.44  % (17193)------------------------------
% 0.21/0.44  % (17188)Success in time 0.078 s
%------------------------------------------------------------------------------
