%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:00 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 881 expanded)
%              Number of leaves         :   14 ( 312 expanded)
%              Depth                    :   17
%              Number of atoms          :  370 (6135 expanded)
%              Number of equality atoms :   65 ( 948 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f901,plain,(
    $false ),
    inference(subsumption_resolution,[],[f900,f452])).

fof(f452,plain,(
    m1_subset_1(sK5(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f274,f301])).

fof(f301,plain,(
    r1_tarski(k1_tarski(sK2),sK1) ),
    inference(resolution,[],[f287,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f287,plain,(
    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f140,f119])).

fof(f119,plain,(
    k1_tarski(sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f118,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

% (8360)Refutation not found, incomplete strategy% (8360)------------------------------
% (8360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (8360)Termination reason: Refutation not found, incomplete strategy

% (8360)Memory used [KB]: 11513
% (8360)Time elapsed: 0.177 s
% (8360)------------------------------
% (8360)------------------------------
% (8446)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
fof(f28,plain,
    ( ! [X3] :
        ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
        | ~ v4_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
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
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ! [X3] :
              ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ! [X3] :
          ( k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
          | ~ v4_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f118,plain,
    ( k1_tarski(sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f93,f43])).

fof(f43,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_tarski(X0) = k3_xboole_0(sK3(sK0,sK1,X0),sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f92,f76])).

fof(f76,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),sK1,X0) = k3_xboole_0(X0,sK1) ),
    inference(forward_demodulation,[],[f75,f73])).

fof(f73,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(resolution,[],[f61,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f75,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),sK1,X0) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
    inference(resolution,[],[f62,f40])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f91,f39])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f90,f40])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f47,f41])).

fof(f41,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
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
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

fof(f140,plain,(
    ! [X4,X5] : m1_subset_1(k3_xboole_0(X5,X4),k1_zfmisc_1(X4)) ),
    inference(forward_demodulation,[],[f131,f130])).

fof(f130,plain,(
    ! [X2,X3] : k9_subset_1(X2,X3,X2) = k3_xboole_0(X3,X2) ),
    inference(resolution,[],[f67,f61])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f59,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f131,plain,(
    ! [X4,X5] : m1_subset_1(k9_subset_1(X4,X5,X4),k1_zfmisc_1(X4)) ),
    inference(resolution,[],[f67,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f274,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | m1_subset_1(sK5(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f116,f119])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(X0,sK1),sK1)
      | m1_subset_1(sK5(sK0,sK1,k3_xboole_0(X0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f89,f74])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f72,f73])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f60,f40])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | m1_subset_1(sK5(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f88,f39])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f40])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK5(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f48,f41])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
                    & v4_pre_topc(sK5(X0,X1,X4),X0)
                    & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
        & v4_pre_topc(sK5(X0,X1,X4),X0)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f900,plain,(
    ~ m1_subset_1(sK5(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f898,f458])).

fof(f458,plain,(
    k1_tarski(sK2) = k3_xboole_0(sK5(sK0,sK1,k1_tarski(sK2)),sK1) ),
    inference(resolution,[],[f276,f301])).

fof(f276,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | k1_tarski(sK2) = k3_xboole_0(sK5(sK0,sK1,k1_tarski(sK2)),sK1) ),
    inference(superposition,[],[f126,f119])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(X0,sK1),sK1)
      | k3_xboole_0(X0,sK1) = k3_xboole_0(sK5(sK0,sK1,k3_xboole_0(X0,sK1)),sK1) ) ),
    inference(resolution,[],[f97,f74])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k3_xboole_0(sK5(sK0,sK1,X0),sK1) = X0 ) ),
    inference(forward_demodulation,[],[f96,f76])).

fof(f96,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f95,f39])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f50,f41])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f898,plain,
    ( k1_tarski(sK2) != k3_xboole_0(sK5(sK0,sK1,k1_tarski(sK2)),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f413,f77])).

fof(f77,plain,(
    ! [X3] :
      ( ~ v4_pre_topc(X3,sK0)
      | k1_tarski(sK2) != k3_xboole_0(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f44,f76])).

fof(f44,plain,(
    ! [X3] :
      ( ~ v4_pre_topc(X3,sK0)
      | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f413,plain,(
    v4_pre_topc(sK5(sK0,sK1,k1_tarski(sK2)),sK0) ),
    inference(resolution,[],[f232,f301])).

fof(f232,plain,
    ( ~ r1_tarski(k1_tarski(sK2),sK1)
    | v4_pre_topc(sK5(sK0,sK1,k1_tarski(sK2)),sK0) ),
    inference(superposition,[],[f109,f119])).

fof(f109,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(X0,sK1),sK1)
      | v4_pre_topc(sK5(sK0,sK1,k3_xboole_0(X0,sK1)),sK0) ) ),
    inference(resolution,[],[f83,f74])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | v4_pre_topc(sK5(sK0,sK1,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f82,f39])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(sK5(sK0,sK1,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f81,f40])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(sK5(sK0,sK1,X0),sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f49,f41])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(sK5(X0,X1,X4),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n011.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:13:27 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (8346)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.49  % (8341)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (8338)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (8346)Refutation not found, incomplete strategy% (8346)------------------------------
% 0.21/0.51  % (8346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8357)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (8346)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8346)Memory used [KB]: 10874
% 0.21/0.51  % (8346)Time elapsed: 0.100 s
% 0.21/0.51  % (8346)------------------------------
% 0.21/0.51  % (8346)------------------------------
% 0.21/0.51  % (8350)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (8355)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (8336)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (8342)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (8339)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (8343)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (8337)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (8340)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (8360)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (8358)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (8353)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (8347)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (8362)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (8366)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (8361)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (8352)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (8365)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (8364)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (8363)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (8345)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (8356)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (8354)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (8344)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (8351)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (8348)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (8359)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (8353)Refutation not found, incomplete strategy% (8353)------------------------------
% 0.21/0.56  % (8353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8353)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8353)Memory used [KB]: 10746
% 0.21/0.56  % (8353)Time elapsed: 0.158 s
% 0.21/0.56  % (8353)------------------------------
% 0.21/0.56  % (8353)------------------------------
% 0.21/0.57  % (8365)Refutation not found, incomplete strategy% (8365)------------------------------
% 0.21/0.57  % (8365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (8365)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (8365)Memory used [KB]: 10874
% 0.21/0.57  % (8365)Time elapsed: 0.142 s
% 0.21/0.57  % (8365)------------------------------
% 0.21/0.57  % (8365)------------------------------
% 1.89/0.61  % (8343)Refutation found. Thanks to Tanya!
% 1.89/0.61  % SZS status Theorem for theBenchmark
% 1.89/0.61  % SZS output start Proof for theBenchmark
% 1.89/0.61  fof(f901,plain,(
% 1.89/0.61    $false),
% 1.89/0.61    inference(subsumption_resolution,[],[f900,f452])).
% 1.89/0.61  fof(f452,plain,(
% 1.89/0.61    m1_subset_1(sK5(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.61    inference(resolution,[],[f274,f301])).
% 1.89/0.61  fof(f301,plain,(
% 1.89/0.61    r1_tarski(k1_tarski(sK2),sK1)),
% 1.89/0.61    inference(resolution,[],[f287,f58])).
% 1.89/0.61  fof(f58,plain,(
% 1.89/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.89/0.61    inference(cnf_transformation,[],[f38])).
% 1.89/0.61  fof(f38,plain,(
% 1.89/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.89/0.61    inference(nnf_transformation,[],[f7])).
% 1.89/0.61  fof(f7,axiom,(
% 1.89/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.89/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.89/0.61  fof(f287,plain,(
% 1.89/0.61    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(sK1))),
% 1.89/0.61    inference(superposition,[],[f140,f119])).
% 1.89/0.61  fof(f119,plain,(
% 1.89/0.61    k1_tarski(sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1)),
% 1.89/0.61    inference(subsumption_resolution,[],[f118,f42])).
% 1.89/0.61  fof(f42,plain,(
% 1.89/0.61    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.89/0.61    inference(cnf_transformation,[],[f28])).
% 1.89/0.62  % (8360)Refutation not found, incomplete strategy% (8360)------------------------------
% 1.89/0.62  % (8360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (8360)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.62  
% 1.89/0.62  % (8360)Memory used [KB]: 11513
% 1.89/0.62  % (8360)Time elapsed: 0.177 s
% 1.89/0.62  % (8360)------------------------------
% 1.89/0.62  % (8360)------------------------------
% 1.89/0.62  % (8446)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.03/0.63  fof(f28,plain,(
% 2.03/0.63    ((! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f27,f26,f25])).
% 2.03/0.63  fof(f25,plain,(
% 2.03/0.63    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f26,plain,(
% 2.03/0.63    ? [X1] : (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),X1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f27,plain,(
% 2.03/0.63    ? [X2] : (! [X3] : (k1_tarski(X2) != k9_subset_1(u1_struct_0(sK0),sK1,X3) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (! [X3] : (k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~v4_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f15,plain,(
% 2.03/0.63    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.03/0.63    inference(flattening,[],[f14])).
% 2.03/0.63  fof(f14,plain,(
% 2.03/0.63    ? [X0] : (? [X1] : ((? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k1_tarski(X2) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.03/0.63    inference(ennf_transformation,[],[f12])).
% 2.03/0.63  fof(f12,negated_conjecture,(
% 2.03/0.63    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 2.03/0.63    inference(negated_conjecture,[],[f11])).
% 2.03/0.63  fof(f11,conjecture,(
% 2.03/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v4_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tex_2)).
% 2.03/0.63  fof(f118,plain,(
% 2.03/0.63    k1_tarski(sK2) = k3_xboole_0(sK3(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 2.03/0.63    inference(resolution,[],[f93,f43])).
% 2.03/0.63  fof(f43,plain,(
% 2.03/0.63    r2_hidden(sK2,sK1)),
% 2.03/0.63    inference(cnf_transformation,[],[f28])).
% 2.03/0.63  fof(f93,plain,(
% 2.03/0.63    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_tarski(X0) = k3_xboole_0(sK3(sK0,sK1,X0),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 2.03/0.63    inference(forward_demodulation,[],[f92,f76])).
% 2.03/0.63  fof(f76,plain,(
% 2.03/0.63    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,X0) = k3_xboole_0(X0,sK1)) )),
% 2.03/0.63    inference(forward_demodulation,[],[f75,f73])).
% 2.03/0.63  fof(f73,plain,(
% 2.03/0.63    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)) )),
% 2.03/0.63    inference(resolution,[],[f61,f40])).
% 2.03/0.63  fof(f40,plain,(
% 2.03/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.03/0.63    inference(cnf_transformation,[],[f28])).
% 2.03/0.63  fof(f61,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f21])).
% 2.03/0.63  fof(f21,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.03/0.63    inference(ennf_transformation,[],[f6])).
% 2.03/0.63  fof(f6,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.03/0.63  fof(f75,plain,(
% 2.03/0.63    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),sK1,X0) = k9_subset_1(u1_struct_0(sK0),X0,sK1)) )),
% 2.03/0.63    inference(resolution,[],[f62,f40])).
% 2.03/0.63  fof(f62,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f22])).
% 2.03/0.63  fof(f22,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.03/0.63    inference(ennf_transformation,[],[f4])).
% 2.03/0.63  fof(f4,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 2.03/0.63  fof(f92,plain,(
% 2.03/0.63    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0))) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f91,f39])).
% 2.03/0.63  fof(f39,plain,(
% 2.03/0.63    l1_pre_topc(sK0)),
% 2.03/0.63    inference(cnf_transformation,[],[f28])).
% 2.03/0.63  fof(f91,plain,(
% 2.03/0.63    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0)) | ~l1_pre_topc(sK0)) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f90,f40])).
% 2.03/0.63  fof(f90,plain,(
% 2.03/0.63    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,sK3(sK0,sK1,X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.03/0.63    inference(resolution,[],[f47,f41])).
% 2.03/0.63  fof(f41,plain,(
% 2.03/0.63    v2_tex_2(sK1,sK0)),
% 2.03/0.63    inference(cnf_transformation,[],[f28])).
% 2.03/0.63  fof(f47,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (~v2_tex_2(X1,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f30])).
% 2.03/0.63  fof(f30,plain,(
% 2.03/0.63    ! [X0] : (! [X1] : (! [X2] : ((k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f29])).
% 2.03/0.63  fof(f29,plain,(
% 2.03/0.63    ! [X2,X1,X0] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tarski(X2) = k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X2)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.03/0.63    introduced(choice_axiom,[])).
% 2.03/0.63  fof(f17,plain,(
% 2.03/0.63    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.63    inference(flattening,[],[f16])).
% 2.03/0.63  fof(f16,plain,(
% 2.03/0.63    ! [X0] : (! [X1] : ((! [X2] : ((? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.63    inference(ennf_transformation,[],[f13])).
% 2.03/0.63  fof(f13,plain,(
% 2.03/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2)) & r2_hidden(X2,X1))))))),
% 2.03/0.63    inference(pure_predicate_removal,[],[f10])).
% 2.03/0.63  fof(f10,axiom,(
% 2.03/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k1_tarski(X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))))))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).
% 2.03/0.63  fof(f140,plain,(
% 2.03/0.63    ( ! [X4,X5] : (m1_subset_1(k3_xboole_0(X5,X4),k1_zfmisc_1(X4))) )),
% 2.03/0.63    inference(forward_demodulation,[],[f131,f130])).
% 2.03/0.63  fof(f130,plain,(
% 2.03/0.63    ( ! [X2,X3] : (k9_subset_1(X2,X3,X2) = k3_xboole_0(X3,X2)) )),
% 2.03/0.63    inference(resolution,[],[f67,f61])).
% 2.03/0.63  fof(f67,plain,(
% 2.03/0.63    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.03/0.63    inference(resolution,[],[f59,f64])).
% 2.03/0.63  fof(f64,plain,(
% 2.03/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.03/0.63    inference(equality_resolution,[],[f56])).
% 2.03/0.63  fof(f56,plain,(
% 2.03/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.03/0.63    inference(cnf_transformation,[],[f37])).
% 2.03/0.63  fof(f37,plain,(
% 2.03/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.63    inference(flattening,[],[f36])).
% 2.03/0.63  fof(f36,plain,(
% 2.03/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.63    inference(nnf_transformation,[],[f1])).
% 2.03/0.63  fof(f1,axiom,(
% 2.03/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.03/0.63  fof(f59,plain,(
% 2.03/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f38])).
% 2.03/0.63  fof(f131,plain,(
% 2.03/0.63    ( ! [X4,X5] : (m1_subset_1(k9_subset_1(X4,X5,X4),k1_zfmisc_1(X4))) )),
% 2.03/0.63    inference(resolution,[],[f67,f60])).
% 2.03/0.63  fof(f60,plain,(
% 2.03/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 2.03/0.63    inference(cnf_transformation,[],[f20])).
% 2.03/0.63  fof(f20,plain,(
% 2.03/0.63    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.03/0.63    inference(ennf_transformation,[],[f5])).
% 2.03/0.63  fof(f5,axiom,(
% 2.03/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.03/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 2.03/0.63  fof(f274,plain,(
% 2.03/0.63    ~r1_tarski(k1_tarski(sK2),sK1) | m1_subset_1(sK5(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.03/0.63    inference(superposition,[],[f116,f119])).
% 2.03/0.63  fof(f116,plain,(
% 2.03/0.63    ( ! [X0] : (~r1_tarski(k3_xboole_0(X0,sK1),sK1) | m1_subset_1(sK5(sK0,sK1,k3_xboole_0(X0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.03/0.63    inference(resolution,[],[f89,f74])).
% 2.03/0.63  fof(f74,plain,(
% 2.03/0.63    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.03/0.63    inference(backward_demodulation,[],[f72,f73])).
% 2.03/0.63  fof(f72,plain,(
% 2.03/0.63    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.03/0.63    inference(resolution,[],[f60,f40])).
% 2.03/0.63  fof(f89,plain,(
% 2.03/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | m1_subset_1(sK5(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f88,f39])).
% 2.03/0.63  fof(f88,plain,(
% 2.03/0.63    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.03/0.63    inference(subsumption_resolution,[],[f87,f40])).
% 2.03/0.63  fof(f87,plain,(
% 2.03/0.63    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK5(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.03/0.63    inference(resolution,[],[f48,f41])).
% 2.03/0.63  fof(f48,plain,(
% 2.03/0.63    ( ! [X4,X0,X1] : (~v2_tex_2(X1,X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.63    inference(cnf_transformation,[],[f35])).
% 2.03/0.63  fof(f35,plain,(
% 2.03/0.63    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X0) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f34,f33])).
% 2.03/0.64  fof(f33,plain,(
% 2.03/0.64    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK4(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f34,plain,(
% 2.03/0.64    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 & v4_pre_topc(sK5(X0,X1,X4),X0) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f32,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(rectify,[],[f31])).
% 2.03/0.64  fof(f31,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f19])).
% 2.03/0.64  fof(f19,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(flattening,[],[f18])).
% 2.03/0.64  fof(f18,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(ennf_transformation,[],[f9])).
% 2.03/0.64  fof(f9,axiom,(
% 2.03/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tex_2)).
% 2.03/0.64  fof(f900,plain,(
% 2.03/0.64    ~m1_subset_1(sK5(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.03/0.64    inference(subsumption_resolution,[],[f898,f458])).
% 2.03/0.64  fof(f458,plain,(
% 2.03/0.64    k1_tarski(sK2) = k3_xboole_0(sK5(sK0,sK1,k1_tarski(sK2)),sK1)),
% 2.03/0.64    inference(resolution,[],[f276,f301])).
% 2.03/0.64  fof(f276,plain,(
% 2.03/0.64    ~r1_tarski(k1_tarski(sK2),sK1) | k1_tarski(sK2) = k3_xboole_0(sK5(sK0,sK1,k1_tarski(sK2)),sK1)),
% 2.03/0.64    inference(superposition,[],[f126,f119])).
% 2.03/0.64  fof(f126,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_tarski(k3_xboole_0(X0,sK1),sK1) | k3_xboole_0(X0,sK1) = k3_xboole_0(sK5(sK0,sK1,k3_xboole_0(X0,sK1)),sK1)) )),
% 2.03/0.64    inference(resolution,[],[f97,f74])).
% 2.03/0.64  fof(f97,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k3_xboole_0(sK5(sK0,sK1,X0),sK1) = X0) )),
% 2.03/0.64    inference(forward_demodulation,[],[f96,f76])).
% 2.03/0.64  fof(f96,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f95,f39])).
% 2.03/0.64  fof(f95,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0 | ~l1_pre_topc(sK0)) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f94,f40])).
% 2.03/0.64  fof(f94,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,sK5(sK0,sK1,X0)) = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.03/0.64    inference(resolution,[],[f50,f41])).
% 2.03/0.64  fof(f50,plain,(
% 2.03/0.64    ( ! [X4,X0,X1] : (~v2_tex_2(X1,X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,sK5(X0,X1,X4)) = X4 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f35])).
% 2.03/0.64  fof(f898,plain,(
% 2.03/0.64    k1_tarski(sK2) != k3_xboole_0(sK5(sK0,sK1,k1_tarski(sK2)),sK1) | ~m1_subset_1(sK5(sK0,sK1,k1_tarski(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.03/0.64    inference(resolution,[],[f413,f77])).
% 2.03/0.64  fof(f77,plain,(
% 2.03/0.64    ( ! [X3] : (~v4_pre_topc(X3,sK0) | k1_tarski(sK2) != k3_xboole_0(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.03/0.64    inference(backward_demodulation,[],[f44,f76])).
% 2.03/0.64  fof(f44,plain,(
% 2.03/0.64    ( ! [X3] : (~v4_pre_topc(X3,sK0) | k9_subset_1(u1_struct_0(sK0),sK1,X3) != k1_tarski(sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f28])).
% 2.03/0.64  fof(f413,plain,(
% 2.03/0.64    v4_pre_topc(sK5(sK0,sK1,k1_tarski(sK2)),sK0)),
% 2.03/0.64    inference(resolution,[],[f232,f301])).
% 2.03/0.64  fof(f232,plain,(
% 2.03/0.64    ~r1_tarski(k1_tarski(sK2),sK1) | v4_pre_topc(sK5(sK0,sK1,k1_tarski(sK2)),sK0)),
% 2.03/0.64    inference(superposition,[],[f109,f119])).
% 2.03/0.64  fof(f109,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_tarski(k3_xboole_0(X0,sK1),sK1) | v4_pre_topc(sK5(sK0,sK1,k3_xboole_0(X0,sK1)),sK0)) )),
% 2.03/0.64    inference(resolution,[],[f83,f74])).
% 2.03/0.64  fof(f83,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | v4_pre_topc(sK5(sK0,sK1,X0),sK0)) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f82,f39])).
% 2.03/0.64  fof(f82,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK5(sK0,sK1,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f81,f40])).
% 2.03/0.64  fof(f81,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK5(sK0,sK1,X0),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 2.03/0.64    inference(resolution,[],[f49,f41])).
% 2.03/0.64  fof(f49,plain,(
% 2.03/0.64    ( ! [X4,X0,X1] : (~v2_tex_2(X1,X0) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(sK5(X0,X1,X4),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f35])).
% 2.03/0.64  % SZS output end Proof for theBenchmark
% 2.03/0.64  % (8343)------------------------------
% 2.03/0.64  % (8343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.64  % (8343)Termination reason: Refutation
% 2.03/0.64  
% 2.03/0.64  % (8343)Memory used [KB]: 2686
% 2.03/0.64  % (8343)Time elapsed: 0.189 s
% 2.03/0.64  % (8343)------------------------------
% 2.03/0.64  % (8343)------------------------------
% 2.03/0.65  % (8333)Success in time 0.285 s
%------------------------------------------------------------------------------
