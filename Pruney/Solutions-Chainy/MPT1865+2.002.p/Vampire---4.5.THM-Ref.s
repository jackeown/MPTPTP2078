%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:00 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 255 expanded)
%              Number of leaves         :    9 (  59 expanded)
%              Depth                    :   12
%              Number of atoms          :  149 (1085 expanded)
%              Number of equality atoms :   30 ( 205 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f122,f121,f123,f49])).

fof(f49,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_tarski(sK2,sK2)
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(definition_unfolding,[],[f26,f36])).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                              & v4_pre_topc(X3,X0) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                            & v4_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).

fof(f123,plain,(
    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_tarski(sK2,sK2))) ),
    inference(unit_resulting_resolution,[],[f31,f30,f29,f99,f118,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).

fof(f118,plain,(
    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f117,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f117,plain,(
    r1_tarski(k2_tarski(sK2,sK2),u1_struct_0(sK0)) ),
    inference(superposition,[],[f47,f103])).

fof(f103,plain,(
    k2_tarski(sK2,sK2) = k3_xboole_0(u1_struct_0(sK0),k2_tarski(sK2,sK2)) ),
    inference(superposition,[],[f73,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f73,plain,(
    k2_tarski(sK2,sK2) = k3_xboole_0(k2_tarski(sK2,sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f68,f52])).

fof(f52,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | k2_tarski(X2,X2) = k3_xboole_0(k2_tarski(X2,X2),X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k2_tarski(X0,X0) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 != X2
      | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ( X0 != X2
        & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f68,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f27,f66,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f66,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f28,f29,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f28,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f27,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f99,plain,(
    r1_tarski(k2_tarski(sK2,sK2),sK1) ),
    inference(superposition,[],[f47,f81])).

fof(f81,plain,(
    k2_tarski(sK2,sK2) = k3_xboole_0(sK1,k2_tarski(sK2,sK2)) ),
    inference(superposition,[],[f57,f32])).

fof(f57,plain,(
    k2_tarski(sK2,sK2) = k3_xboole_0(k2_tarski(sK2,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f28,f52])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f121,plain,(
    m1_subset_1(sK4(sK0,sK1,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f31,f30,f99,f29,f118,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f122,plain,(
    v4_pre_topc(sK4(sK0,sK1,k2_tarski(sK2,sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f31,f30,f29,f99,f118,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v4_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n020.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 16:27:52 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.48  % (912)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.23/0.49  % (921)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.52  % (922)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.23/0.52  % (938)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.23/0.53  % (914)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.23/0.54  % (911)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.54  % (930)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.54  % (935)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.23/0.54  % (913)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.23/0.54  % (918)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.23/0.54  % (910)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.54  % (931)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.23/0.54  % (929)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.23/0.54  % (913)Refutation found. Thanks to Tanya!
% 1.23/0.54  % SZS status Theorem for theBenchmark
% 1.23/0.54  % SZS output start Proof for theBenchmark
% 1.23/0.54  fof(f151,plain,(
% 1.23/0.54    $false),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f122,f121,f123,f49])).
% 1.23/0.54  fof(f49,plain,(
% 1.23/0.54    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k2_tarski(sK2,sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.23/0.54    inference(definition_unfolding,[],[f26,f36])).
% 1.23/0.54  fof(f36,plain,(
% 1.23/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f6])).
% 1.23/0.54  fof(f6,axiom,(
% 1.23/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.23/0.54  fof(f26,plain,(
% 1.23/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f17])).
% 1.23/0.54  fof(f17,plain,(
% 1.23/0.54    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.23/0.54    inference(flattening,[],[f16])).
% 1.23/0.54  fof(f16,plain,(
% 1.23/0.54    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.23/0.54    inference(ennf_transformation,[],[f14])).
% 1.23/0.54  fof(f14,negated_conjecture,(
% 1.23/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.23/0.54    inference(negated_conjecture,[],[f13])).
% 1.23/0.54  fof(f13,conjecture,(
% 1.23/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).
% 1.23/0.54  fof(f123,plain,(
% 1.23/0.54    k2_tarski(sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k2_tarski(sK2,sK2)))),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f31,f30,f29,f99,f118,f40])).
% 1.23/0.54  fof(f40,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2 | ~v2_tex_2(X1,X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f21])).
% 1.23/0.54  fof(f21,plain,(
% 1.23/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.54    inference(flattening,[],[f20])).
% 1.23/0.54  fof(f20,plain,(
% 1.23/0.54    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.54    inference(ennf_transformation,[],[f12])).
% 1.23/0.54  fof(f12,axiom,(
% 1.23/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 1.23/0.54  fof(f118,plain,(
% 1.23/0.54    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f117,f44])).
% 1.23/0.54  fof(f44,plain,(
% 1.23/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f9])).
% 1.23/0.54  fof(f9,axiom,(
% 1.23/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.23/0.54  fof(f117,plain,(
% 1.23/0.54    r1_tarski(k2_tarski(sK2,sK2),u1_struct_0(sK0))),
% 1.23/0.54    inference(superposition,[],[f47,f103])).
% 1.23/0.54  fof(f103,plain,(
% 1.23/0.54    k2_tarski(sK2,sK2) = k3_xboole_0(u1_struct_0(sK0),k2_tarski(sK2,sK2))),
% 1.23/0.54    inference(superposition,[],[f73,f32])).
% 1.23/0.54  fof(f32,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f1])).
% 1.23/0.54  fof(f1,axiom,(
% 1.23/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.23/0.54  fof(f73,plain,(
% 1.23/0.54    k2_tarski(sK2,sK2) = k3_xboole_0(k2_tarski(sK2,sK2),u1_struct_0(sK0))),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f68,f52])).
% 1.23/0.54  fof(f52,plain,(
% 1.23/0.54    ( ! [X2,X1] : (~r2_hidden(X2,X1) | k2_tarski(X2,X2) = k3_xboole_0(k2_tarski(X2,X2),X1)) )),
% 1.23/0.54    inference(equality_resolution,[],[f50])).
% 1.23/0.54  fof(f50,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k2_tarski(X0,X0) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 1.23/0.54    inference(definition_unfolding,[],[f35,f36])).
% 1.23/0.54  fof(f35,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 != X2 | k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f19])).
% 1.23/0.54  fof(f19,plain,(
% 1.23/0.54    ! [X0,X1,X2] : (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 1.23/0.54    inference(flattening,[],[f18])).
% 1.23/0.54  fof(f18,plain,(
% 1.23/0.54    ! [X0,X1,X2] : ((k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))) | ~r2_hidden(X0,X1))),
% 1.23/0.54    inference(ennf_transformation,[],[f7])).
% 1.23/0.54  fof(f7,axiom,(
% 1.23/0.54    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 1.23/0.54  fof(f68,plain,(
% 1.23/0.54    r2_hidden(sK2,u1_struct_0(sK0))),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f27,f66,f48])).
% 1.23/0.54  fof(f48,plain,(
% 1.23/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X0,X1) | r2_hidden(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f25])).
% 1.23/0.54  fof(f25,plain,(
% 1.23/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.23/0.54    inference(flattening,[],[f24])).
% 1.23/0.54  fof(f24,plain,(
% 1.23/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.23/0.54    inference(ennf_transformation,[],[f8])).
% 1.23/0.54  fof(f8,axiom,(
% 1.23/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.23/0.54  fof(f66,plain,(
% 1.23/0.54    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f28,f29,f46])).
% 1.23/0.54  fof(f46,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f23])).
% 1.23/0.54  fof(f23,plain,(
% 1.23/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.23/0.54    inference(ennf_transformation,[],[f10])).
% 1.23/0.54  fof(f10,axiom,(
% 1.23/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.23/0.54  fof(f28,plain,(
% 1.23/0.54    r2_hidden(sK2,sK1)),
% 1.23/0.54    inference(cnf_transformation,[],[f17])).
% 1.23/0.54  fof(f27,plain,(
% 1.23/0.54    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.23/0.54    inference(cnf_transformation,[],[f17])).
% 1.23/0.54  fof(f47,plain,(
% 1.23/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f3])).
% 1.23/0.54  fof(f3,axiom,(
% 1.23/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.23/0.54  fof(f99,plain,(
% 1.23/0.54    r1_tarski(k2_tarski(sK2,sK2),sK1)),
% 1.23/0.54    inference(superposition,[],[f47,f81])).
% 1.23/0.54  fof(f81,plain,(
% 1.23/0.54    k2_tarski(sK2,sK2) = k3_xboole_0(sK1,k2_tarski(sK2,sK2))),
% 1.23/0.54    inference(superposition,[],[f57,f32])).
% 1.23/0.54  fof(f57,plain,(
% 1.23/0.54    k2_tarski(sK2,sK2) = k3_xboole_0(k2_tarski(sK2,sK2),sK1)),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f28,f52])).
% 1.23/0.54  fof(f29,plain,(
% 1.23/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.23/0.54    inference(cnf_transformation,[],[f17])).
% 1.23/0.54  fof(f30,plain,(
% 1.23/0.54    v2_tex_2(sK1,sK0)),
% 1.23/0.54    inference(cnf_transformation,[],[f17])).
% 1.23/0.54  fof(f31,plain,(
% 1.23/0.54    l1_pre_topc(sK0)),
% 1.23/0.54    inference(cnf_transformation,[],[f17])).
% 1.23/0.54  fof(f121,plain,(
% 1.23/0.54    m1_subset_1(sK4(sK0,sK1,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f31,f30,f99,f29,f118,f38])).
% 1.23/0.54  fof(f38,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f21])).
% 1.23/0.54  fof(f122,plain,(
% 1.23/0.54    v4_pre_topc(sK4(sK0,sK1,k2_tarski(sK2,sK2)),sK0)),
% 1.23/0.54    inference(unit_resulting_resolution,[],[f31,f30,f29,f99,f118,f39])).
% 1.23/0.54  fof(f39,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | v4_pre_topc(sK4(X0,X1,X2),X0) | ~v2_tex_2(X1,X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f21])).
% 1.23/0.54  % SZS output end Proof for theBenchmark
% 1.23/0.54  % (913)------------------------------
% 1.23/0.54  % (913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (913)Termination reason: Refutation
% 1.23/0.54  
% 1.23/0.54  % (913)Memory used [KB]: 6268
% 1.23/0.54  % (913)Time elapsed: 0.122 s
% 1.23/0.54  % (913)------------------------------
% 1.23/0.54  % (913)------------------------------
% 1.23/0.55  % (908)Success in time 0.171 s
%------------------------------------------------------------------------------
