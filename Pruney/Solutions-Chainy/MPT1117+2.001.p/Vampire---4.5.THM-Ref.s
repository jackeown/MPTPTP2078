%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 161 expanded)
%              Number of leaves         :    8 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  179 ( 639 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(global_subsumption,[],[f79,f107])).

fof(f107,plain,(
    r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) ),
    inference(resolution,[],[f76,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X0) ) ),
    inference(resolution,[],[f52,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f52,plain,(
    r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(resolution,[],[f24,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f24,plain,(
    ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X1,k2_pre_topc(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(X1,k2_pre_topc(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ~ r1_tarski(X1,k2_pre_topc(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k2_pre_topc(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f76,plain,(
    r1_tarski(sK1,sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) ),
    inference(global_subsumption,[],[f58,f75])).

fof(f75,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f74,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f63,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_tarski(X1,sK2(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( ~ r2_hidden(X2,sK2(X0,X1,X2))
                    & r1_tarski(X1,sK2(X0,X1,X2))
                    & v4_pre_topc(sK2(X0,X1,X2),X0)
                    & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X2,sK2(X0,X1,X2))
        & r1_tarski(X1,sK2(X0,X1,X2))
        & v4_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( ~ r2_hidden(X2,X3)
                      & r1_tarski(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( r2_hidden(X2,X3)
                      | ~ r1_tarski(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( r2_hidden(X2,X3)
                    | ~ r1_tarski(X1,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( r2_hidden(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r1_tarski(X1,X3)
                        & v4_pre_topc(X3,X0) )
                     => r2_hidden(X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).

fof(f53,plain,(
    ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f52,f45])).

fof(f45,plain,(
    ! [X8] :
      ( ~ r2_hidden(X8,sK1)
      | r2_hidden(X8,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f23,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f79,plain,(
    ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) ),
    inference(global_subsumption,[],[f58,f78])).

fof(f78,plain,
    ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f77,f22])).

fof(f77,plain,
    ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f64,f23])).

fof(f64,plain,
    ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))
    | ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,sK2(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.41  % (6624)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.41  % (6624)Refutation found. Thanks to Tanya!
% 0.22/0.41  % SZS status Theorem for theBenchmark
% 0.22/0.41  % SZS output start Proof for theBenchmark
% 0.22/0.41  fof(f110,plain,(
% 0.22/0.41    $false),
% 0.22/0.41    inference(global_subsumption,[],[f79,f107])).
% 0.22/0.41  fof(f107,plain,(
% 0.22/0.41    r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))),
% 0.22/0.41    inference(resolution,[],[f76,f59])).
% 0.22/0.41  fof(f59,plain,(
% 0.22/0.41    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X0)) )),
% 0.22/0.41    inference(resolution,[],[f52,f31])).
% 0.22/0.41  fof(f31,plain,(
% 0.22/0.41    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f21])).
% 0.22/0.41  fof(f21,plain,(
% 0.22/0.41    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 0.22/0.41  fof(f20,plain,(
% 0.22/0.41    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f19,plain,(
% 0.22/0.41    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.41    inference(rectify,[],[f18])).
% 0.22/0.41  fof(f18,plain,(
% 0.22/0.41    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.41    inference(nnf_transformation,[],[f10])).
% 0.22/0.41  fof(f10,plain,(
% 0.22/0.41    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.41    inference(ennf_transformation,[],[f1])).
% 0.22/0.41  fof(f1,axiom,(
% 0.22/0.41    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.41  fof(f52,plain,(
% 0.22/0.41    r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK1)),
% 0.22/0.41    inference(resolution,[],[f24,f32])).
% 0.22/0.41  fof(f32,plain,(
% 0.22/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f21])).
% 0.22/0.41  fof(f24,plain,(
% 0.22/0.41    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.22/0.41    inference(cnf_transformation,[],[f13])).
% 0.22/0.41  fof(f13,plain,(
% 0.22/0.41    (~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).
% 0.22/0.41  fof(f11,plain,(
% 0.22/0.41    ? [X0] : (? [X1] : (~r1_tarski(X1,k2_pre_topc(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(X1,k2_pre_topc(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f12,plain,(
% 0.22/0.41    ? [X1] : (~r1_tarski(X1,k2_pre_topc(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f6,plain,(
% 0.22/0.41    ? [X0] : (? [X1] : (~r1_tarski(X1,k2_pre_topc(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.41    inference(ennf_transformation,[],[f5])).
% 0.22/0.41  fof(f5,negated_conjecture,(
% 0.22/0.41    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.22/0.41    inference(negated_conjecture,[],[f4])).
% 0.22/0.41  fof(f4,conjecture,(
% 0.22/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.22/0.41  fof(f76,plain,(
% 0.22/0.41    r1_tarski(sK1,sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))),
% 0.22/0.41    inference(global_subsumption,[],[f58,f75])).
% 0.22/0.41  fof(f75,plain,(
% 0.22/0.41    r1_tarski(sK1,sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) | ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.41    inference(subsumption_resolution,[],[f74,f22])).
% 0.22/0.41  fof(f22,plain,(
% 0.22/0.41    l1_pre_topc(sK0)),
% 0.22/0.41    inference(cnf_transformation,[],[f13])).
% 0.22/0.41  fof(f74,plain,(
% 0.22/0.41    r1_tarski(sK1,sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) | ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.41    inference(subsumption_resolution,[],[f63,f23])).
% 0.22/0.41  fof(f23,plain,(
% 0.22/0.41    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.41    inference(cnf_transformation,[],[f13])).
% 0.22/0.41  fof(f63,plain,(
% 0.22/0.41    r1_tarski(sK1,sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) | ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.41    inference(resolution,[],[f53,f28])).
% 0.22/0.41  fof(f28,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r1_tarski(X1,sK2(X0,X1,X2)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f17])).
% 0.22/0.41  fof(f17,plain,(
% 0.22/0.41    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (~r2_hidden(X2,sK2(X0,X1,X2)) & r1_tarski(X1,sK2(X0,X1,X2)) & v4_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 0.22/0.41  fof(f16,plain,(
% 0.22/0.41    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X2,sK2(X0,X1,X2)) & r1_tarski(X1,sK2(X0,X1,X2)) & v4_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.41    introduced(choice_axiom,[])).
% 0.22/0.41  fof(f15,plain,(
% 0.22/0.41    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.41    inference(rectify,[],[f14])).
% 0.22/0.41  fof(f14,plain,(
% 0.22/0.41    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.41    inference(nnf_transformation,[],[f8])).
% 0.22/0.41  fof(f8,plain,(
% 0.22/0.41    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.41    inference(flattening,[],[f7])).
% 0.22/0.41  fof(f7,plain,(
% 0.22/0.41    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : ((r2_hidden(X2,X3) | (~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.41    inference(ennf_transformation,[],[f3])).
% 0.22/0.41  fof(f3,axiom,(
% 0.22/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (r2_hidden(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) => r2_hidden(X2,X3)))))))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).
% 0.22/0.41  fof(f53,plain,(
% 0.22/0.41    ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))),
% 0.22/0.41    inference(resolution,[],[f24,f33])).
% 0.22/0.41  fof(f33,plain,(
% 0.22/0.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f21])).
% 0.22/0.41  fof(f58,plain,(
% 0.22/0.41    r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.41    inference(resolution,[],[f52,f45])).
% 0.22/0.41  fof(f45,plain,(
% 0.22/0.41    ( ! [X8] : (~r2_hidden(X8,sK1) | r2_hidden(X8,u1_struct_0(sK0))) )),
% 0.22/0.41    inference(resolution,[],[f23,f30])).
% 0.22/0.41  fof(f30,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.41    inference(cnf_transformation,[],[f9])).
% 0.22/0.41  fof(f9,plain,(
% 0.22/0.41    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.41    inference(ennf_transformation,[],[f2])).
% 0.22/0.41  fof(f2,axiom,(
% 0.22/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.41  fof(f79,plain,(
% 0.22/0.41    ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1))))),
% 0.22/0.41    inference(global_subsumption,[],[f58,f78])).
% 0.22/0.41  fof(f78,plain,(
% 0.22/0.41    ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) | ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.41    inference(subsumption_resolution,[],[f77,f22])).
% 0.22/0.41  fof(f77,plain,(
% 0.22/0.41    ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) | ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.22/0.41    inference(subsumption_resolution,[],[f64,f23])).
% 0.22/0.41  fof(f64,plain,(
% 0.22/0.41    ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,sK3(sK1,k2_pre_topc(sK0,sK1)))) | ~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.41    inference(resolution,[],[f53,f29])).
% 0.22/0.41  fof(f29,plain,(
% 0.22/0.41    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,sK2(X0,X1,X2)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.41    inference(cnf_transformation,[],[f17])).
% 0.22/0.41  % SZS output end Proof for theBenchmark
% 0.22/0.41  % (6624)------------------------------
% 0.22/0.41  % (6624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.41  % (6624)Termination reason: Refutation
% 0.22/0.41  
% 0.22/0.41  % (6624)Memory used [KB]: 5500
% 0.22/0.41  % (6624)Time elapsed: 0.006 s
% 0.22/0.41  % (6624)------------------------------
% 0.22/0.41  % (6624)------------------------------
% 0.22/0.42  % (6612)Success in time 0.056 s
%------------------------------------------------------------------------------
