%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  76 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 ( 333 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(subsumption_resolution,[],[f232,f24])).

fof(f24,plain,(
    ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))
    & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
                & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2))
            & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2))
          & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2))
        & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))
      & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
                 => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
               => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).

fof(f232,plain,(
    r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(superposition,[],[f41,f223])).

fof(f223,plain,(
    k5_setfam_1(u1_struct_0(sK0),sK2) = k2_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK2),k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f221,f26])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f221,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK2) = k2_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK2),k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))
    | ~ r1_tarski(k5_setfam_1(u1_struct_0(sK0),sK2),k2_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK2),k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))) ),
    inference(resolution,[],[f208,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f208,plain,(
    r1_tarski(k2_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK2),k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))),k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(resolution,[],[f51,f33])).

fof(f33,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f51,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),sK2))
      | r1_tarski(k2_xboole_0(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))),k5_setfam_1(u1_struct_0(sK0),sK2)) ) ),
    inference(resolution,[],[f49,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f49,plain,(
    r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),k5_setfam_1(u1_struct_0(sK0),sK2)) ),
    inference(resolution,[],[f38,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X0)),k1_tops_2(sK0,X0,sK2)),k5_setfam_1(u1_struct_0(sK0),sK2)) ) ),
    inference(subsumption_resolution,[],[f37,f20])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X0] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X0)),k1_tops_2(sK0,X0,sK2)),k5_setfam_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X2] : r1_tarski(sK1,k2_xboole_0(X2,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))) ),
    inference(resolution,[],[f23,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f23,plain,(
    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:43:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (21658)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.46  % (21650)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (21651)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (21651)Refutation not found, incomplete strategy% (21651)------------------------------
% 0.20/0.48  % (21651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (21651)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (21651)Memory used [KB]: 6140
% 0.20/0.48  % (21651)Time elapsed: 0.084 s
% 0.20/0.48  % (21651)------------------------------
% 0.20/0.48  % (21651)------------------------------
% 0.20/0.49  % (21655)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.49  % (21643)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (21640)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (21649)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (21649)Refutation not found, incomplete strategy% (21649)------------------------------
% 0.20/0.50  % (21649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21649)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21649)Memory used [KB]: 10490
% 0.20/0.50  % (21649)Time elapsed: 0.108 s
% 0.20/0.50  % (21649)------------------------------
% 0.20/0.50  % (21649)------------------------------
% 0.20/0.50  % (21638)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (21662)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.50  % (21638)Refutation not found, incomplete strategy% (21638)------------------------------
% 0.20/0.50  % (21638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21638)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21638)Memory used [KB]: 10490
% 0.20/0.50  % (21638)Time elapsed: 0.103 s
% 0.20/0.50  % (21638)------------------------------
% 0.20/0.50  % (21638)------------------------------
% 0.20/0.50  % (21652)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (21659)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (21663)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (21645)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (21653)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (21641)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (21661)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (21646)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (21660)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (21644)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (21642)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (21644)Refutation not found, incomplete strategy% (21644)------------------------------
% 0.20/0.52  % (21644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21644)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (21644)Memory used [KB]: 10490
% 0.20/0.52  % (21644)Time elapsed: 0.092 s
% 0.20/0.52  % (21644)------------------------------
% 0.20/0.52  % (21644)------------------------------
% 0.20/0.52  % (21656)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (21639)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (21657)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (21654)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (21639)Refutation not found, incomplete strategy% (21639)------------------------------
% 0.20/0.52  % (21639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21639)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (21639)Memory used [KB]: 10618
% 0.20/0.52  % (21639)Time elapsed: 0.124 s
% 0.20/0.52  % (21639)------------------------------
% 0.20/0.52  % (21639)------------------------------
% 0.20/0.52  % (21648)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (21647)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (21646)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f251,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f232,f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ((~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f16,f15,f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X1)),k1_tops_2(sK0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X2] : (~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),X2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2)) & r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(flattening,[],[f8])).
% 0.20/0.53  fof(f8,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,negated_conjecture,(
% 0.20/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f6])).
% 0.20/0.53  fof(f6,conjecture,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2))) => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).
% 0.20/0.53  fof(f232,plain,(
% 0.20/0.53    r1_tarski(sK1,k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.20/0.53    inference(superposition,[],[f41,f223])).
% 0.20/0.53  fof(f223,plain,(
% 0.20/0.53    k5_setfam_1(u1_struct_0(sK0),sK2) = k2_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK2),k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))),
% 0.20/0.53    inference(subsumption_resolution,[],[f221,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.53  fof(f221,plain,(
% 0.20/0.53    k5_setfam_1(u1_struct_0(sK0),sK2) = k2_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK2),k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))) | ~r1_tarski(k5_setfam_1(u1_struct_0(sK0),sK2),k2_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK2),k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))))),
% 0.20/0.53    inference(resolution,[],[f208,f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(flattening,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.53  fof(f208,plain,(
% 0.20/0.53    r1_tarski(k2_xboole_0(k5_setfam_1(u1_struct_0(sK0),sK2),k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))),k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.20/0.53    inference(resolution,[],[f51,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.53    inference(equality_resolution,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X1] : (~r1_tarski(X1,k5_setfam_1(u1_struct_0(sK0),sK2)) | r1_tarski(k2_xboole_0(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))),k5_setfam_1(u1_struct_0(sK0),sK2))) )),
% 0.20/0.53    inference(resolution,[],[f49,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)),k5_setfam_1(u1_struct_0(sK0),sK2))),
% 0.20/0.53    inference(resolution,[],[f38,f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X0)),k1_tops_2(sK0,X0,sK2)),k5_setfam_1(u1_struct_0(sK0),sK2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f37,f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,X0)),k1_tops_2(sK0,X0,sK2)),k5_setfam_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.20/0.53    inference(resolution,[],[f22,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X2] : (r1_tarski(sK1,k2_xboole_0(X2,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2))))) )),
% 0.20/0.53    inference(resolution,[],[f23,f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    r1_tarski(sK1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK0,sK1)),k1_tops_2(sK0,sK1,sK2)))),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (21646)------------------------------
% 0.20/0.53  % (21646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (21646)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (21646)Memory used [KB]: 1791
% 0.20/0.53  % (21646)Time elapsed: 0.115 s
% 0.20/0.53  % (21646)------------------------------
% 0.20/0.53  % (21646)------------------------------
% 0.20/0.53  % (21637)Success in time 0.176 s
%------------------------------------------------------------------------------
