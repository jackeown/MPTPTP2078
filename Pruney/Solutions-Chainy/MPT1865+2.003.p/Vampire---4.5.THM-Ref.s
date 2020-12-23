%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:00 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 309 expanded)
%              Number of leaves         :   10 (  81 expanded)
%              Depth                    :   23
%              Number of atoms          :  186 (1014 expanded)
%              Number of equality atoms :   32 ( 213 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(subsumption_resolution,[],[f332,f22])).

fof(f22,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f332,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f331,f23])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f331,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f330,f51])).

fof(f51,plain,(
    r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) ),
    inference(resolution,[],[f20,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f20,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f330,plain,
    ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f329,f99])).

fof(f99,plain,(
    m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f68,f59])).

fof(f59,plain,(
    k1_enumset1(sK2,sK2,sK2) = k1_setfam_1(k1_enumset1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK2),sK1)) ),
    inference(resolution,[],[f51,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f68,plain,(
    ! [X2] : m1_subset_1(k1_setfam_1(k1_enumset1(X2,X2,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f64,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

% (18738)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,sK1)),u1_struct_0(sK0)) ),
    inference(superposition,[],[f53,f43])).

fof(f43,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0)) ),
    inference(definition_unfolding,[],[f31,f40,f40])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f52,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1) ) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f52,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f21,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f329,plain,
    ( ~ m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f328,f21])).

fof(f328,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f327,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f327,plain,(
    ~ m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f326,f22])).

fof(f326,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f325,f21])).

fof(f325,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f324,f51])).

fof(f324,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f323,f99])).

fof(f323,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f184,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(sK4(sK0,X0,X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f23,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v4_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f184,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(trivial_inequality_removal,[],[f182])).

fof(f182,plain,
    ( k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2)
    | ~ v4_pre_topc(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),sK0)
    | ~ m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f42,f158])).

fof(f158,plain,(
    k1_enumset1(sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2))) ),
    inference(subsumption_resolution,[],[f155,f99])).

fof(f155,plain,
    ( ~ m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_enumset1(sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2))) ),
    inference(resolution,[],[f116,f51])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f113,f21])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X0)) = X0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f49,f22])).

fof(f49,plain,(
    ! [X2,X3] :
      ( ~ v2_tex_2(X2,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,X2)
      | k9_subset_1(u1_struct_0(sK0),X2,sK4(sK0,X2,X3)) = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_enumset1(sK2,sK2,sK2)
      | ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(definition_unfolding,[],[f18,f41])).

fof(f18,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:36:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (18731)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.48  % (18729)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.50  % (18739)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (18745)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (18737)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (18753)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.56  % (18725)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.56  % (18745)Refutation found. Thanks to Tanya!
% 1.30/0.56  % SZS status Theorem for theBenchmark
% 1.30/0.56  % SZS output start Proof for theBenchmark
% 1.30/0.56  fof(f333,plain,(
% 1.30/0.56    $false),
% 1.30/0.56    inference(subsumption_resolution,[],[f332,f22])).
% 1.30/0.56  fof(f22,plain,(
% 1.30/0.56    v2_tex_2(sK1,sK0)),
% 1.30/0.56    inference(cnf_transformation,[],[f13])).
% 1.30/0.56  fof(f13,plain,(
% 1.30/0.56    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.30/0.56    inference(flattening,[],[f12])).
% 1.30/0.56  fof(f12,plain,(
% 1.30/0.56    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.30/0.56    inference(ennf_transformation,[],[f11])).
% 1.30/0.56  fof(f11,negated_conjecture,(
% 1.30/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.30/0.56    inference(negated_conjecture,[],[f10])).
% 1.30/0.56  fof(f10,conjecture,(
% 1.30/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 1.30/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).
% 1.30/0.56  fof(f332,plain,(
% 1.30/0.56    ~v2_tex_2(sK1,sK0)),
% 1.30/0.56    inference(subsumption_resolution,[],[f331,f23])).
% 1.30/0.56  fof(f23,plain,(
% 1.30/0.56    l1_pre_topc(sK0)),
% 1.30/0.56    inference(cnf_transformation,[],[f13])).
% 1.30/0.56  fof(f331,plain,(
% 1.30/0.56    ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)),
% 1.30/0.56    inference(subsumption_resolution,[],[f330,f51])).
% 1.30/0.56  fof(f51,plain,(
% 1.30/0.56    r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1)),
% 1.30/0.56    inference(resolution,[],[f20,f46])).
% 1.30/0.56  fof(f46,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_enumset1(X0,X0,X0),X1)) )),
% 1.30/0.56    inference(definition_unfolding,[],[f35,f41])).
% 1.30/0.56  fof(f41,plain,(
% 1.30/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.30/0.56    inference(definition_unfolding,[],[f24,f33])).
% 1.30/0.56  fof(f33,plain,(
% 1.30/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f5])).
% 1.30/0.56  fof(f5,axiom,(
% 1.30/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.30/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.56  fof(f24,plain,(
% 1.30/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f4])).
% 1.30/0.56  fof(f4,axiom,(
% 1.30/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.30/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.30/0.56  fof(f35,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f6])).
% 1.30/0.56  fof(f6,axiom,(
% 1.30/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.30/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.30/0.56  fof(f20,plain,(
% 1.30/0.56    r2_hidden(sK2,sK1)),
% 1.30/0.56    inference(cnf_transformation,[],[f13])).
% 1.30/0.56  fof(f330,plain,(
% 1.30/0.56    ~r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)),
% 1.30/0.56    inference(subsumption_resolution,[],[f329,f99])).
% 1.30/0.56  fof(f99,plain,(
% 1.30/0.56    m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.30/0.56    inference(superposition,[],[f68,f59])).
% 1.30/0.56  fof(f59,plain,(
% 1.30/0.56    k1_enumset1(sK2,sK2,sK2) = k1_setfam_1(k1_enumset1(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK2,sK2,sK2),sK1))),
% 1.30/0.56    inference(resolution,[],[f51,f44])).
% 1.30/0.56  fof(f44,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k1_enumset1(X0,X0,X1)) = X0) )),
% 1.30/0.56    inference(definition_unfolding,[],[f34,f40])).
% 1.30/0.56  fof(f40,plain,(
% 1.30/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.30/0.56    inference(definition_unfolding,[],[f32,f33])).
% 1.30/0.56  fof(f32,plain,(
% 1.30/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.30/0.56    inference(cnf_transformation,[],[f7])).
% 1.30/0.56  fof(f7,axiom,(
% 1.30/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.30/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.30/0.56  fof(f34,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.30/0.56    inference(cnf_transformation,[],[f16])).
% 1.30/0.56  fof(f16,plain,(
% 1.30/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.30/0.56    inference(ennf_transformation,[],[f3])).
% 1.30/0.56  fof(f3,axiom,(
% 1.30/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.30/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.30/0.56  fof(f68,plain,(
% 1.30/0.56    ( ! [X2] : (m1_subset_1(k1_setfam_1(k1_enumset1(X2,X2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.30/0.56    inference(resolution,[],[f64,f37])).
% 1.30/0.56  fof(f37,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.30/0.56    inference(cnf_transformation,[],[f8])).
% 1.30/0.56  % (18738)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.56  fof(f8,axiom,(
% 1.30/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.30/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.30/0.56  fof(f64,plain,(
% 1.30/0.56    ( ! [X0] : (r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,sK1)),u1_struct_0(sK0))) )),
% 1.30/0.56    inference(superposition,[],[f53,f43])).
% 1.30/0.56  fof(f43,plain,(
% 1.30/0.56    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k1_setfam_1(k1_enumset1(X1,X1,X0))) )),
% 1.30/0.56    inference(definition_unfolding,[],[f31,f40,f40])).
% 1.30/0.56  fof(f31,plain,(
% 1.30/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f1])).
% 1.30/0.56  fof(f1,axiom,(
% 1.30/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.30/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.30/0.56  fof(f53,plain,(
% 1.30/0.56    ( ! [X0] : (r1_tarski(k1_setfam_1(k1_enumset1(sK1,sK1,X0)),u1_struct_0(sK0))) )),
% 1.30/0.56    inference(resolution,[],[f52,f47])).
% 1.30/0.56  fof(f47,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_setfam_1(k1_enumset1(X0,X0,X2)),X1)) )),
% 1.30/0.56    inference(definition_unfolding,[],[f39,f40])).
% 1.30/0.56  fof(f39,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f17])).
% 1.30/0.56  fof(f17,plain,(
% 1.30/0.56    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.30/0.56    inference(ennf_transformation,[],[f2])).
% 1.30/0.56  fof(f2,axiom,(
% 1.30/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.30/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.30/0.56  fof(f52,plain,(
% 1.30/0.56    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.30/0.56    inference(resolution,[],[f21,f38])).
% 1.30/0.56  fof(f38,plain,(
% 1.30/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f8])).
% 1.30/0.56  fof(f21,plain,(
% 1.30/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.30/0.56    inference(cnf_transformation,[],[f13])).
% 1.30/0.56  fof(f329,plain,(
% 1.30/0.56    ~m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)),
% 1.30/0.56    inference(subsumption_resolution,[],[f328,f21])).
% 1.30/0.56  fof(f328,plain,(
% 1.30/0.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) | ~l1_pre_topc(sK0) | ~v2_tex_2(sK1,sK0)),
% 1.30/0.56    inference(resolution,[],[f327,f26])).
% 1.30/0.56  fof(f26,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~l1_pre_topc(X0) | ~v2_tex_2(X1,X0)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f15])).
% 1.30/0.56  fof(f15,plain,(
% 1.30/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.30/0.56    inference(flattening,[],[f14])).
% 1.30/0.56  fof(f14,plain,(
% 1.30/0.56    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.30/0.56    inference(ennf_transformation,[],[f9])).
% 1.30/0.56  fof(f9,axiom,(
% 1.30/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.30/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 1.30/0.56  fof(f327,plain,(
% 1.30/0.56    ~m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.30/0.56    inference(subsumption_resolution,[],[f326,f22])).
% 1.30/0.56  fof(f326,plain,(
% 1.30/0.56    ~m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0)),
% 1.30/0.56    inference(subsumption_resolution,[],[f325,f21])).
% 1.30/0.56  fof(f325,plain,(
% 1.30/0.56    ~m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0)),
% 1.30/0.56    inference(subsumption_resolution,[],[f324,f51])).
% 1.30/0.56  fof(f324,plain,(
% 1.30/0.56    ~m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0)),
% 1.30/0.56    inference(subsumption_resolution,[],[f323,f99])).
% 1.30/0.56  fof(f323,plain,(
% 1.30/0.56    ~m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_enumset1(sK2,sK2,sK2),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0)),
% 1.30/0.56    inference(resolution,[],[f184,f48])).
% 1.30/0.56  fof(f48,plain,(
% 1.30/0.56    ( ! [X0,X1] : (v4_pre_topc(sK4(sK0,X0,X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0)) )),
% 1.30/0.56    inference(resolution,[],[f23,f27])).
% 1.30/0.56  fof(f27,plain,(
% 1.30/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | v4_pre_topc(sK4(X0,X1,X2),X0) | ~v2_tex_2(X1,X0)) )),
% 1.30/0.56    inference(cnf_transformation,[],[f15])).
% 1.30/0.56  fof(f184,plain,(
% 1.30/0.56    ~v4_pre_topc(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.30/0.56    inference(trivial_inequality_removal,[],[f182])).
% 1.30/0.56  fof(f182,plain,(
% 1.30/0.56    k1_enumset1(sK2,sK2,sK2) != k1_enumset1(sK2,sK2,sK2) | ~v4_pre_topc(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),sK0) | ~m1_subset_1(sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.30/0.56    inference(superposition,[],[f42,f158])).
% 1.30/0.56  fof(f158,plain,(
% 1.30/0.56    k1_enumset1(sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)))),
% 1.30/0.56    inference(subsumption_resolution,[],[f155,f99])).
% 1.30/0.56  fof(f155,plain,(
% 1.30/0.56    ~m1_subset_1(k1_enumset1(sK2,sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | k1_enumset1(sK2,sK2,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,k1_enumset1(sK2,sK2,sK2)))),
% 1.30/0.56    inference(resolution,[],[f116,f51])).
% 1.30/0.57  fof(f116,plain,(
% 1.30/0.57    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X0)) = X0) )),
% 1.30/0.57    inference(subsumption_resolution,[],[f113,f21])).
% 1.30/0.57  fof(f113,plain,(
% 1.30/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,sK4(sK0,sK1,X0)) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.30/0.57    inference(resolution,[],[f49,f22])).
% 1.30/0.57  fof(f49,plain,(
% 1.30/0.57    ( ! [X2,X3] : (~v2_tex_2(X2,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,X2) | k9_subset_1(u1_struct_0(sK0),X2,sK4(sK0,X2,X3)) = X3 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.30/0.57    inference(resolution,[],[f23,f28])).
% 1.30/0.57  fof(f28,plain,(
% 1.30/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2 | ~v2_tex_2(X1,X0)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f15])).
% 1.30/0.57  fof(f42,plain,(
% 1.30/0.57    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_enumset1(sK2,sK2,sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.30/0.57    inference(definition_unfolding,[],[f18,f41])).
% 1.30/0.57  fof(f18,plain,(
% 1.30/0.57    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)) )),
% 1.30/0.57    inference(cnf_transformation,[],[f13])).
% 1.30/0.57  % SZS output end Proof for theBenchmark
% 1.30/0.57  % (18745)------------------------------
% 1.30/0.57  % (18745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.57  % (18745)Termination reason: Refutation
% 1.30/0.57  
% 1.30/0.57  % (18745)Memory used [KB]: 1918
% 1.30/0.57  % (18745)Time elapsed: 0.163 s
% 1.30/0.57  % (18745)------------------------------
% 1.30/0.57  % (18745)------------------------------
% 1.30/0.57  % (18750)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.57  % (18727)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.57  % (18748)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.57  % (18724)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.57  % (18723)Success in time 0.209 s
%------------------------------------------------------------------------------
