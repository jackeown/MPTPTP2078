%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 166 expanded)
%              Number of leaves         :    8 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 (1062 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f24,f28,f40,f57,f26,f38,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | v3_pre_topc(X3,X0)
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

fof(f38,plain,(
    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f24,f29,f25,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    r2_hidden(sK3(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f55,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f55,plain,(
    r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2) ),
    inference(unit_resulting_resolution,[],[f27,f50,f37])).

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

fof(f50,plain,(
    r1_tarski(k1_tarski(sK3(sK0,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f39,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    r2_hidden(sK3(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f24,f29,f25,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1),X1)
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ~ v3_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f24,f29,f25,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v3_pre_topc(sK3(X0,X1),X0)
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    v1_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:23:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (25837)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.46  % (25837)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f24,f28,f40,f57,f26,f38,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_2(X1,X0) | v3_pre_topc(X3,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0,X1),X0) & r2_hidden(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(rectify,[],[f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    m1_subset_1(sK3(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f24,f29,f25,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ((~v1_tops_2(sK1,sK0) & v1_tops_2(sK2,sK0) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(X1,X0) & v1_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_2(X1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ? [X1] : (? [X2] : (~v1_tops_2(X1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (~v1_tops_2(sK1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ? [X2] : (~v1_tops_2(sK1,sK0) & v1_tops_2(X2,sK0) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (~v1_tops_2(sK1,sK0) & v1_tops_2(sK2,sK0) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_2(X1,X0) & v1_tops_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_2(X1,X0) & (v1_tops_2(X2,X0) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.20/0.46    inference(negated_conjecture,[],[f5])).
% 0.20/0.46  fof(f5,conjecture,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_tops_2(X2,X0) & r1_tarski(X1,X2)) => v1_tops_2(X1,X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tops_2)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ~v1_tops_2(sK1,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    r2_hidden(sK3(sK0,sK1),sK2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f55,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.46    inference(nnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    r1_tarski(k1_tarski(sK3(sK0,sK1)),sK2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f27,f50,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    r1_tarski(k1_tarski(sK3(sK0,sK1)),sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f39,f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    r2_hidden(sK3(sK0,sK1),sK1)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f24,f29,f25,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1),X1) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    r1_tarski(sK1,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ~v3_pre_topc(sK3(sK0,sK1),sK0)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f24,f29,f25,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(sK3(X0,X1),X0) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    v1_tops_2(sK2,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    l1_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (25837)------------------------------
% 0.20/0.46  % (25837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (25837)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (25837)Memory used [KB]: 895
% 0.20/0.46  % (25837)Time elapsed: 0.044 s
% 0.20/0.46  % (25837)------------------------------
% 0.20/0.46  % (25837)------------------------------
% 0.20/0.46  % (25831)Success in time 0.109 s
%------------------------------------------------------------------------------
