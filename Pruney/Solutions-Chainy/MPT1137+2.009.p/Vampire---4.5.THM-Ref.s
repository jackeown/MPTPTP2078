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
% DateTime   : Thu Dec  3 13:09:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 269 expanded)
%              Number of leaves         :    9 (  52 expanded)
%              Depth                    :   18
%              Number of atoms          :  196 (1286 expanded)
%              Number of equality atoms :   17 ( 146 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(subsumption_resolution,[],[f123,f24])).

fof(f24,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                    & r1_orders_2(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f123,plain,(
    sK1 = sK2 ),
    inference(resolution,[],[f98,f91])).

fof(f91,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f81,f49])).

fof(f49,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f21,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f21,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f80,f76])).

fof(f76,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f75,f60])).

fof(f60,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f25,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f72,f50])).

fof(f50,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f21,f43])).

fof(f72,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f71,f24])).

fof(f71,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | sK1 = sK2
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f69,f58])).

fof(f58,plain,(
    r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f57,f27])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f56,f25])).

fof(f56,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f55,f21])).

fof(f55,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f23,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f23,plain,(
    r1_orders_2(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | sK1 = sK2
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,(
    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f53,f27])).

fof(f53,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f52,f21])).

fof(f52,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f51,f25])).

fof(f51,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f22,f36])).

fof(f22,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0))
      | X0 = X1
      | ~ v1_relat_1(u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f47,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_relat_2(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | ~ r2_hidden(k4_tarski(X3,X2),X0)
      | X2 = X3
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

fof(f47,plain,(
    r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f46,f27])).

fof(f46,plain,
    ( r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f26,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v5_orders_2(X0)
      | r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

fof(f26,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f80,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f77,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f77,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f48,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f48,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f98,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | sK1 = X1 ) ),
    inference(resolution,[],[f90,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f90,plain,(
    v1_xboole_0(sK1) ),
    inference(resolution,[],[f81,f59])).

fof(f59,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f25,f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:40:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (16178)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (16180)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (16179)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (16179)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f123,f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    sK1 != sK2),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.20/0.50    inference(negated_conjecture,[],[f9])).
% 0.20/0.50  fof(f9,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    sK1 = sK2),
% 0.20/0.50    inference(resolution,[],[f98,f91])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    v1_xboole_0(sK2)),
% 0.20/0.50    inference(resolution,[],[f81,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK2)),
% 0.20/0.50    inference(resolution,[],[f21,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f80,f76])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ~v1_relat_1(u1_orders_2(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f75,f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    r2_hidden(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f25,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v1_relat_1(u1_orders_2(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f72,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    r2_hidden(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.50    inference(resolution,[],[f21,f43])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ~r2_hidden(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v1_relat_1(u1_orders_2(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f71,f24])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ~r2_hidden(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK1,u1_struct_0(sK0)) | sK1 = sK2 | ~v1_relat_1(u1_orders_2(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f69,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f57,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    l1_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f56,f25])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f55,f21])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.50    inference(resolution,[],[f23,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    r1_orders_2(sK0,sK2,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ~r2_hidden(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0)) | sK1 = sK2 | ~v1_relat_1(u1_orders_2(sK0))),
% 0.20/0.50    inference(resolution,[],[f62,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f53,f27])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f52,f21])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f51,f25])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.50    inference(resolution,[],[f22,f36])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    r1_orders_2(sK0,sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~r2_hidden(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0)) | X0 = X1 | ~v1_relat_1(u1_orders_2(sK0))) )),
% 0.20/0.50    inference(resolution,[],[f47,f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~r4_relat_2(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(k4_tarski(X3,X2),X0) | X2 = X3 | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : ((r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => X2 = X3)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f46,f27])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    r4_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.20/0.50    inference(resolution,[],[f26,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ( ! [X0] : (~v5_orders_2(X0) | r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : ((v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (l1_orders_2(X0) => (v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    v5_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    v1_relat_1(u1_orders_2(sK0))),
% 0.20/0.50    inference(subsumption_resolution,[],[f77,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) | v1_relat_1(u1_orders_2(sK0))),
% 0.20/0.50    inference(resolution,[],[f48,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.20/0.50    inference(resolution,[],[f27,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X1] : (~v1_xboole_0(X1) | sK1 = X1) )),
% 0.20/0.50    inference(resolution,[],[f90,f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    v1_xboole_0(sK1)),
% 0.20/0.50    inference(resolution,[],[f81,f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK1)),
% 0.20/0.50    inference(resolution,[],[f25,f41])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (16179)------------------------------
% 0.20/0.50  % (16179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16179)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (16179)Memory used [KB]: 6140
% 0.20/0.50  % (16179)Time elapsed: 0.089 s
% 0.20/0.50  % (16179)------------------------------
% 0.20/0.50  % (16179)------------------------------
% 0.20/0.50  % (16176)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (16173)Success in time 0.141 s
%------------------------------------------------------------------------------
