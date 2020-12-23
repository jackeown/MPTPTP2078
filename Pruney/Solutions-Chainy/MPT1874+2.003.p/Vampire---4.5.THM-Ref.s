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
% DateTime   : Thu Dec  3 13:21:21 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 155 expanded)
%              Number of leaves         :   13 (  54 expanded)
%              Depth                    :   23
%              Number of atoms          :  284 (1019 expanded)
%              Number of equality atoms :   38 ( 152 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(subsumption_resolution,[],[f124,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & r2_hidden(X2,X1)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & r2_hidden(X2,sK1)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).

fof(f124,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f116,f42])).

fof(f42,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f116,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f88,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f88,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f87,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f87,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f86,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f81,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f57,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f81,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f80,f42])).

fof(f80,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,sK1) ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( k1_tarski(sK2) != k1_tarski(sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,sK1) ),
    inference(superposition,[],[f64,f75])).

fof(f75,plain,(
    ! [X3] :
      ( k1_tarski(X3) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X3)))
      | ~ m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X3,sK1) ) ),
    inference(resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f69,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f68,f39])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f67,f40])).

fof(f40,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f66,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f65,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
                & r1_tarski(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f64,plain,
    ( k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f63,f41])).

fof(f63,plain,
    ( k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f43,f56])).

fof(f43,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:16:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (1209401344)
% 0.15/0.38  ipcrm: permission denied for id (1212678145)
% 0.15/0.38  ipcrm: permission denied for id (1209434114)
% 0.15/0.38  ipcrm: permission denied for id (1209466883)
% 0.22/0.38  ipcrm: permission denied for id (1209532422)
% 0.22/0.38  ipcrm: permission denied for id (1209565191)
% 0.22/0.38  ipcrm: permission denied for id (1215299592)
% 0.22/0.39  ipcrm: permission denied for id (1215365130)
% 0.22/0.39  ipcrm: permission denied for id (1209663499)
% 0.22/0.39  ipcrm: permission denied for id (1215430669)
% 0.22/0.39  ipcrm: permission denied for id (1212973070)
% 0.22/0.39  ipcrm: permission denied for id (1209761807)
% 0.22/0.39  ipcrm: permission denied for id (1213005840)
% 0.22/0.40  ipcrm: permission denied for id (1215463441)
% 0.22/0.40  ipcrm: permission denied for id (1209892882)
% 0.22/0.40  ipcrm: permission denied for id (1209925651)
% 0.22/0.40  ipcrm: permission denied for id (1213071380)
% 0.22/0.40  ipcrm: permission denied for id (1215496213)
% 0.22/0.40  ipcrm: permission denied for id (1216675862)
% 0.22/0.40  ipcrm: permission denied for id (1215561751)
% 0.22/0.40  ipcrm: permission denied for id (1213202456)
% 0.22/0.41  ipcrm: permission denied for id (1213235225)
% 0.22/0.41  ipcrm: permission denied for id (1216708634)
% 0.22/0.41  ipcrm: permission denied for id (1210089500)
% 0.22/0.41  ipcrm: permission denied for id (1216774173)
% 0.22/0.41  ipcrm: permission denied for id (1213366302)
% 0.22/0.41  ipcrm: permission denied for id (1213399071)
% 0.22/0.41  ipcrm: permission denied for id (1210155040)
% 0.22/0.42  ipcrm: permission denied for id (1216806945)
% 0.22/0.42  ipcrm: permission denied for id (1213464610)
% 0.22/0.42  ipcrm: permission denied for id (1210220579)
% 0.22/0.42  ipcrm: permission denied for id (1210253348)
% 0.22/0.42  ipcrm: permission denied for id (1215725605)
% 0.22/0.42  ipcrm: permission denied for id (1210286118)
% 0.22/0.42  ipcrm: permission denied for id (1213530151)
% 0.22/0.42  ipcrm: permission denied for id (1213562920)
% 0.22/0.43  ipcrm: permission denied for id (1213595689)
% 0.22/0.43  ipcrm: permission denied for id (1213628458)
% 0.22/0.43  ipcrm: permission denied for id (1210417195)
% 0.22/0.43  ipcrm: permission denied for id (1213661228)
% 0.22/0.43  ipcrm: permission denied for id (1215758381)
% 0.22/0.43  ipcrm: permission denied for id (1210515502)
% 0.22/0.43  ipcrm: permission denied for id (1210548271)
% 0.22/0.43  ipcrm: permission denied for id (1216839728)
% 0.22/0.44  ipcrm: permission denied for id (1213792306)
% 0.22/0.44  ipcrm: permission denied for id (1210679347)
% 0.22/0.44  ipcrm: permission denied for id (1213825076)
% 0.22/0.44  ipcrm: permission denied for id (1210744885)
% 0.22/0.44  ipcrm: permission denied for id (1210777654)
% 0.22/0.44  ipcrm: permission denied for id (1210810423)
% 0.22/0.44  ipcrm: permission denied for id (1210843192)
% 0.22/0.44  ipcrm: permission denied for id (1213857849)
% 0.22/0.45  ipcrm: permission denied for id (1215856698)
% 0.22/0.45  ipcrm: permission denied for id (1215922235)
% 0.22/0.45  ipcrm: permission denied for id (1215987773)
% 0.22/0.45  ipcrm: permission denied for id (1216938046)
% 0.22/0.45  ipcrm: permission denied for id (1211072575)
% 0.22/0.45  ipcrm: permission denied for id (1214087232)
% 0.22/0.46  ipcrm: permission denied for id (1211138113)
% 0.22/0.46  ipcrm: permission denied for id (1211170882)
% 0.22/0.46  ipcrm: permission denied for id (1216086083)
% 0.22/0.46  ipcrm: permission denied for id (1211269188)
% 0.22/0.46  ipcrm: permission denied for id (1214185541)
% 0.22/0.46  ipcrm: permission denied for id (1211301958)
% 0.22/0.46  ipcrm: permission denied for id (1211334727)
% 0.22/0.46  ipcrm: permission denied for id (1211367496)
% 0.22/0.47  ipcrm: permission denied for id (1214218313)
% 0.22/0.47  ipcrm: permission denied for id (1214251082)
% 0.22/0.47  ipcrm: permission denied for id (1211465803)
% 0.22/0.47  ipcrm: permission denied for id (1211498572)
% 0.22/0.47  ipcrm: permission denied for id (1211531341)
% 0.22/0.47  ipcrm: permission denied for id (1211564110)
% 0.22/0.47  ipcrm: permission denied for id (1211596879)
% 0.22/0.47  ipcrm: permission denied for id (1211629648)
% 0.22/0.48  ipcrm: permission denied for id (1211662417)
% 0.22/0.48  ipcrm: permission denied for id (1214283858)
% 0.22/0.48  ipcrm: permission denied for id (1211695187)
% 0.22/0.48  ipcrm: permission denied for id (1211727956)
% 0.22/0.48  ipcrm: permission denied for id (1211760726)
% 0.22/0.49  ipcrm: permission denied for id (1216151639)
% 0.22/0.49  ipcrm: permission denied for id (1211826264)
% 0.22/0.49  ipcrm: permission denied for id (1214382169)
% 0.22/0.49  ipcrm: permission denied for id (1211859034)
% 0.22/0.49  ipcrm: permission denied for id (1214414939)
% 0.22/0.49  ipcrm: permission denied for id (1211891804)
% 0.22/0.49  ipcrm: permission denied for id (1217003613)
% 0.22/0.50  ipcrm: permission denied for id (1211957342)
% 0.22/0.50  ipcrm: permission denied for id (1214513248)
% 0.22/0.50  ipcrm: permission denied for id (1214546017)
% 0.22/0.50  ipcrm: permission denied for id (1216249954)
% 0.22/0.50  ipcrm: permission denied for id (1216282723)
% 0.22/0.51  ipcrm: permission denied for id (1216315492)
% 0.22/0.51  ipcrm: permission denied for id (1214677093)
% 0.22/0.51  ipcrm: permission denied for id (1214709862)
% 0.22/0.51  ipcrm: permission denied for id (1216381031)
% 0.22/0.51  ipcrm: permission denied for id (1214775400)
% 0.22/0.51  ipcrm: permission denied for id (1214808169)
% 0.22/0.51  ipcrm: permission denied for id (1212088426)
% 0.22/0.52  ipcrm: permission denied for id (1212121195)
% 0.22/0.52  ipcrm: permission denied for id (1212153964)
% 0.22/0.52  ipcrm: permission denied for id (1214840941)
% 0.22/0.52  ipcrm: permission denied for id (1214873710)
% 0.22/0.52  ipcrm: permission denied for id (1212219503)
% 0.22/0.53  ipcrm: permission denied for id (1215004785)
% 0.22/0.53  ipcrm: permission denied for id (1212317810)
% 0.22/0.53  ipcrm: permission denied for id (1212350579)
% 0.22/0.53  ipcrm: permission denied for id (1216446580)
% 0.22/0.53  ipcrm: permission denied for id (1215037557)
% 0.22/0.53  ipcrm: permission denied for id (1212416118)
% 0.22/0.53  ipcrm: permission denied for id (1212448887)
% 0.22/0.54  ipcrm: permission denied for id (1215070328)
% 0.22/0.54  ipcrm: permission denied for id (1217101945)
% 0.22/0.54  ipcrm: permission denied for id (1212514426)
% 0.22/0.54  ipcrm: permission denied for id (1212547195)
% 0.22/0.54  ipcrm: permission denied for id (1216512124)
% 0.22/0.54  ipcrm: permission denied for id (1215168637)
% 0.37/0.54  ipcrm: permission denied for id (1212612734)
% 0.37/0.54  ipcrm: permission denied for id (1215201407)
% 0.40/0.65  % (20238)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.40/0.66  % (20223)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.40/0.67  % (20240)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.40/0.68  % (20234)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.40/0.68  % (20226)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.40/0.68  % (20225)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.40/0.68  % (20226)Refutation not found, incomplete strategy% (20226)------------------------------
% 0.40/0.68  % (20226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.40/0.68  % (20226)Termination reason: Refutation not found, incomplete strategy
% 0.40/0.68  
% 0.40/0.68  % (20226)Memory used [KB]: 10618
% 0.40/0.68  % (20226)Time elapsed: 0.087 s
% 0.40/0.68  % (20226)------------------------------
% 0.40/0.68  % (20226)------------------------------
% 0.40/0.68  % (20242)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.44/0.68  % (20236)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.44/0.68  % (20242)Refutation found. Thanks to Tanya!
% 0.44/0.68  % SZS status Theorem for theBenchmark
% 0.44/0.68  % SZS output start Proof for theBenchmark
% 0.44/0.68  fof(f127,plain,(
% 0.44/0.68    $false),
% 0.44/0.68    inference(subsumption_resolution,[],[f124,f39])).
% 0.44/0.68  fof(f39,plain,(
% 0.44/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.44/0.68    inference(cnf_transformation,[],[f25])).
% 0.44/0.68  fof(f25,plain,(
% 0.44/0.68    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.44/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).
% 0.44/0.68  fof(f22,plain,(
% 0.44/0.68    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.44/0.68    introduced(choice_axiom,[])).
% 0.44/0.68  fof(f23,plain,(
% 0.44/0.68    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.44/0.68    introduced(choice_axiom,[])).
% 0.44/0.68  fof(f24,plain,(
% 0.44/0.68    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.44/0.68    introduced(choice_axiom,[])).
% 0.44/0.68  fof(f12,plain,(
% 0.44/0.68    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.44/0.68    inference(flattening,[],[f11])).
% 0.44/0.68  fof(f11,plain,(
% 0.44/0.68    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.44/0.68    inference(ennf_transformation,[],[f10])).
% 0.44/0.68  fof(f10,negated_conjecture,(
% 0.44/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.44/0.68    inference(negated_conjecture,[],[f9])).
% 0.44/0.68  fof(f9,conjecture,(
% 0.44/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.44/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).
% 0.44/0.68  fof(f124,plain,(
% 0.44/0.68    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.44/0.68    inference(resolution,[],[f116,f42])).
% 0.44/0.68  fof(f42,plain,(
% 0.44/0.68    r2_hidden(sK2,sK1)),
% 0.44/0.68    inference(cnf_transformation,[],[f25])).
% 0.44/0.68  fof(f116,plain,(
% 0.44/0.68    ( ! [X6,X7] : (~r2_hidden(X7,X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.44/0.68    inference(resolution,[],[f88,f49])).
% 0.44/0.68  fof(f49,plain,(
% 0.44/0.68    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.44/0.68    inference(cnf_transformation,[],[f33])).
% 0.44/0.68  fof(f33,plain,(
% 0.44/0.68    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.44/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 0.44/0.68  fof(f32,plain,(
% 0.44/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.44/0.68    introduced(choice_axiom,[])).
% 0.44/0.68  fof(f31,plain,(
% 0.44/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.44/0.68    inference(rectify,[],[f30])).
% 0.44/0.68  fof(f30,plain,(
% 0.44/0.68    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.44/0.68    inference(nnf_transformation,[],[f1])).
% 0.44/0.68  fof(f1,axiom,(
% 0.44/0.68    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.44/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.44/0.68  fof(f88,plain,(
% 0.44/0.68    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.44/0.68    inference(resolution,[],[f87,f44])).
% 0.44/0.68  fof(f44,plain,(
% 0.44/0.68    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.44/0.68    inference(cnf_transformation,[],[f13])).
% 0.44/0.68  fof(f13,plain,(
% 0.44/0.68    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.44/0.68    inference(ennf_transformation,[],[f4])).
% 0.44/0.68  fof(f4,axiom,(
% 0.44/0.68    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.44/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.44/0.68  fof(f87,plain,(
% 0.44/0.68    v1_xboole_0(u1_struct_0(sK0))),
% 0.44/0.68    inference(subsumption_resolution,[],[f86,f41])).
% 0.44/0.68  fof(f41,plain,(
% 0.44/0.68    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.44/0.68    inference(cnf_transformation,[],[f25])).
% 0.44/0.68  fof(f86,plain,(
% 0.44/0.68    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.44/0.68    inference(duplicate_literal_removal,[],[f82])).
% 0.44/0.68  fof(f82,plain,(
% 0.44/0.68    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.44/0.68    inference(resolution,[],[f81,f62])).
% 0.44/0.68  fof(f62,plain,(
% 0.44/0.68    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.44/0.68    inference(duplicate_literal_removal,[],[f61])).
% 0.44/0.68  fof(f61,plain,(
% 0.44/0.68    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.44/0.68    inference(superposition,[],[f57,f56])).
% 0.44/0.68  fof(f56,plain,(
% 0.44/0.68    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.44/0.68    inference(cnf_transformation,[],[f19])).
% 0.44/0.68  fof(f19,plain,(
% 0.44/0.68    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.44/0.68    inference(flattening,[],[f18])).
% 0.44/0.68  fof(f18,plain,(
% 0.44/0.68    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.44/0.68    inference(ennf_transformation,[],[f7])).
% 0.44/0.68  fof(f7,axiom,(
% 0.44/0.68    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.44/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.44/0.68  fof(f57,plain,(
% 0.44/0.68    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.44/0.68    inference(cnf_transformation,[],[f21])).
% 0.44/0.68  fof(f21,plain,(
% 0.44/0.68    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.44/0.68    inference(flattening,[],[f20])).
% 0.44/0.68  fof(f20,plain,(
% 0.44/0.68    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.44/0.68    inference(ennf_transformation,[],[f6])).
% 0.44/0.68  fof(f6,axiom,(
% 0.44/0.68    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.44/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.44/0.68  fof(f81,plain,(
% 0.44/0.68    ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.44/0.68    inference(subsumption_resolution,[],[f80,f42])).
% 0.44/0.68  fof(f80,plain,(
% 0.44/0.68    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,sK1)),
% 0.44/0.68    inference(trivial_inequality_removal,[],[f79])).
% 0.44/0.68  fof(f79,plain,(
% 0.44/0.68    k1_tarski(sK2) != k1_tarski(sK2) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,sK1)),
% 0.44/0.68    inference(superposition,[],[f64,f75])).
% 0.44/0.68  fof(f75,plain,(
% 0.44/0.68    ( ! [X3] : (k1_tarski(X3) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X3))) | ~m1_subset_1(k1_tarski(X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X3,sK1)) )),
% 0.44/0.68    inference(resolution,[],[f70,f55])).
% 0.44/0.68  fof(f55,plain,(
% 0.44/0.68    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.44/0.68    inference(cnf_transformation,[],[f17])).
% 0.44/0.68  fof(f17,plain,(
% 0.44/0.68    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.44/0.68    inference(ennf_transformation,[],[f3])).
% 0.44/0.68  fof(f3,axiom,(
% 0.44/0.68    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.44/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.44/0.68  fof(f70,plain,(
% 0.44/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.44/0.68    inference(resolution,[],[f69,f58])).
% 0.44/0.68  fof(f58,plain,(
% 0.44/0.68    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.44/0.68    inference(cnf_transformation,[],[f35])).
% 0.44/0.68  fof(f35,plain,(
% 0.44/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.44/0.68    inference(nnf_transformation,[],[f5])).
% 0.44/0.68  fof(f5,axiom,(
% 0.44/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.44/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.44/0.68  fof(f69,plain,(
% 0.44/0.68    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 0.44/0.68    inference(subsumption_resolution,[],[f68,f39])).
% 0.44/0.68  fof(f68,plain,(
% 0.44/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 0.44/0.68    inference(resolution,[],[f67,f40])).
% 0.44/0.68  fof(f40,plain,(
% 0.44/0.68    v2_tex_2(sK1,sK0)),
% 0.44/0.68    inference(cnf_transformation,[],[f25])).
% 0.44/0.68  fof(f67,plain,(
% 0.44/0.68    ( ! [X0,X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) )),
% 0.44/0.68    inference(subsumption_resolution,[],[f66,f36])).
% 0.44/0.68  fof(f36,plain,(
% 0.44/0.68    ~v2_struct_0(sK0)),
% 0.44/0.68    inference(cnf_transformation,[],[f25])).
% 0.44/0.68  fof(f66,plain,(
% 0.44/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 0.44/0.68    inference(subsumption_resolution,[],[f65,f37])).
% 0.44/0.68  fof(f37,plain,(
% 0.44/0.68    v2_pre_topc(sK0)),
% 0.44/0.68    inference(cnf_transformation,[],[f25])).
% 0.44/0.68  fof(f65,plain,(
% 0.44/0.68    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.44/0.68    inference(resolution,[],[f45,f38])).
% 0.44/0.68  fof(f38,plain,(
% 0.44/0.68    l1_pre_topc(sK0)),
% 0.44/0.68    inference(cnf_transformation,[],[f25])).
% 0.44/0.68  fof(f45,plain,(
% 0.44/0.68    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.44/0.68    inference(cnf_transformation,[],[f29])).
% 0.44/0.68  fof(f29,plain,(
% 0.44/0.68    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.44/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 0.44/0.68  fof(f28,plain,(
% 0.44/0.68    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.44/0.68    introduced(choice_axiom,[])).
% 0.44/0.68  fof(f27,plain,(
% 0.44/0.68    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.44/0.68    inference(rectify,[],[f26])).
% 0.44/0.68  fof(f26,plain,(
% 0.44/0.68    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.44/0.68    inference(nnf_transformation,[],[f15])).
% 0.44/0.68  fof(f15,plain,(
% 0.44/0.68    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.44/0.68    inference(flattening,[],[f14])).
% 0.44/0.68  fof(f14,plain,(
% 0.44/0.68    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.44/0.68    inference(ennf_transformation,[],[f8])).
% 0.44/0.68  fof(f8,axiom,(
% 0.44/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.44/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.44/0.68  fof(f64,plain,(
% 0.44/0.68    k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.44/0.68    inference(subsumption_resolution,[],[f63,f41])).
% 0.44/0.68  fof(f63,plain,(
% 0.44/0.68    k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.44/0.68    inference(superposition,[],[f43,f56])).
% 0.44/0.68  fof(f43,plain,(
% 0.44/0.68    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.44/0.68    inference(cnf_transformation,[],[f25])).
% 0.44/0.68  % SZS output end Proof for theBenchmark
% 0.44/0.68  % (20242)------------------------------
% 0.44/0.68  % (20242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.44/0.68  % (20242)Termination reason: Refutation
% 0.44/0.68  
% 0.44/0.68  % (20242)Memory used [KB]: 6268
% 0.44/0.68  % (20242)Time elapsed: 0.073 s
% 0.44/0.68  % (20242)------------------------------
% 0.44/0.68  % (20242)------------------------------
% 0.44/0.68  % (20230)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.44/0.68  % (20063)Success in time 0.313 s
%------------------------------------------------------------------------------
