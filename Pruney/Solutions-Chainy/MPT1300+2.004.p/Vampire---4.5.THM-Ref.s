%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:27 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 181 expanded)
%              Number of leaves         :    9 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  176 (1137 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(subsumption_resolution,[],[f47,f44])).

fof(f44,plain,(
    r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f27,f40,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f40,plain,(
    r1_tarski(k1_tarski(sK3(sK0,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f38,plain,(
    r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f24,f29,f25,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK3(X0,X1),X0)
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v1_tops_2(sK1,sK0)
    & v1_tops_2(sK2,sK0)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_2(X1,X0)
                & v1_tops_2(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,sK0)
              & v1_tops_2(X2,sK0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_2(X1,sK0)
            & v1_tops_2(X2,sK0)
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ~ v1_tops_2(sK1,sK0)
          & v1_tops_2(X2,sK0)
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ v1_tops_2(sK1,sK0)
        & v1_tops_2(X2,sK0)
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ~ v1_tops_2(sK1,sK0)
      & v1_tops_2(sK2,sK0)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_2(X1,X0)
              & v1_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v1_tops_2(X2,X0)
                    & r1_tarski(X1,X2) )
                 => v1_tops_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v1_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v1_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).

fof(f29,plain,(
    ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    ~ r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f46,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f46,plain,(
    ~ r2_hidden(sK3(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f24,f28,f26,f41,f39,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f25,f38,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f41,plain,(
    ~ v3_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f29,f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    v1_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:53:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.43  % (4483)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.44  % (4483)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % (4499)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.45  % (4491)WARNING: option uwaf not known.
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f48,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f47,f44])).
% 0.20/0.45  fof(f44,plain,(
% 0.20/0.45    r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f27,f40,f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    r1_tarski(k1_tarski(sK3(sK0,sK1)),sK1)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f38,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.45    inference(nnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    r2_hidden(sK3(sK0,sK1),sK1)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f24,f29,f25,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(rectify,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(nnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ((~v1_tops_2(sK1,sK0) & v1_tops_2(sK2,sK0) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(X1,X0) & v1_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(X1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ? [X1] : (? [X2] : (~v1_tops_2(X1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(sK1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ? [X2] : (~v1_tops_2(sK1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(sK1,sK0) & v1_tops_2(sK2,sK0) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(X1,X0) & v1_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f7])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(X1,X0) & (v1_tops_2(X2,X0) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.20/0.45    inference(negated_conjecture,[],[f5])).
% 0.20/0.45  fof(f5,conjecture,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ~v1_tops_2(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    r1_tarski(sK1,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ~r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f46,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f23])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ~r2_hidden(sK3(sK0,sK1),sK2)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f24,f28,f26,f41,f39,f30])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X0,X3,X1] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f25,f38,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.45  fof(f41,plain,(
% 0.20/0.45    ~v3_pre_topc(sK3(sK0,sK1),sK0)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f24,f29,f25,f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_tops_2(X1,X0) | ~v3_pre_topc(sK3(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f22])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    v1_tops_2(sK2,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (4483)------------------------------
% 0.20/0.45  % (4483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (4483)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (4483)Memory used [KB]: 9850
% 0.20/0.45  % (4483)Time elapsed: 0.057 s
% 0.20/0.45  % (4483)------------------------------
% 0.20/0.45  % (4483)------------------------------
% 0.20/0.45  % (4501)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.20/0.45  % (4478)Success in time 0.104 s
%------------------------------------------------------------------------------
