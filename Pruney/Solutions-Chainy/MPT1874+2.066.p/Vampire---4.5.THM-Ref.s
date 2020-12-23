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
% DateTime   : Thu Dec  3 13:21:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 168 expanded)
%              Number of leaves         :   11 (  61 expanded)
%              Depth                    :   23
%              Number of atoms          :  266 (1152 expanded)
%              Number of equality atoms :   43 ( 175 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(subsumption_resolution,[],[f34,f77])).

fof(f77,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(resolution,[],[f76,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & r2_hidden(sK2,sK1)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19,f18])).

fof(f18,plain,
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

fof(f19,plain,
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

fof(f20,plain,
    ( ? [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & r2_hidden(X2,sK1)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & r2_hidden(sK2,sK1)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f75,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f75,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f52,f73])).

fof(f73,plain,(
    k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) ),
    inference(resolution,[],[f71,f34])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) ) ),
    inference(resolution,[],[f70,f31])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) ) ),
    inference(subsumption_resolution,[],[f69,f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,sK1) ) ),
    inference(resolution,[],[f68,f33])).

fof(f33,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f67,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X3,X1) ) ),
    inference(resolution,[],[f46,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f67,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1)
      | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0))) ) ),
    inference(resolution,[],[f65,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f65,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),u1_struct_0(sK0))
      | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f59,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f56,f31])).

fof(f56,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(resolution,[],[f55,f32])).

fof(f32,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f54,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f53,f29])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1)))
        & r1_tarski(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f52,plain,
    ( k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f51,f33])).

fof(f51,plain,
    ( k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f35,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f35,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:14:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (13665)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.47  % (13665)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f34,f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 0.20/0.47    inference(resolution,[],[f76,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ((k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) & v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ? [X2] : (k6_domain_1(u1_struct_0(sK0),X2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & r2_hidden(X2,sK1) & m1_subset_1(X2,u1_struct_0(sK0))) => (k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & r2_hidden(sK2,sK1) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f7])).
% 0.20/0.47  fof(f7,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tex_2)).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0)) )),
% 0.20/0.47    inference(resolution,[],[f75,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f52,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))),
% 0.20/0.47    inference(resolution,[],[f71,f34])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))) )),
% 0.20/0.47    inference(resolution,[],[f70,f31])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f69,f34])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_tarski(sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | ~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,sK1)) )),
% 0.20/0.47    inference(resolution,[],[f68,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0))) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.47    inference(resolution,[],[f67,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X3,X1)) )),
% 0.20/0.47    inference(resolution,[],[f46,f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_xboole_0(X1) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0)))) )),
% 0.20/0.47    inference(resolution,[],[f65,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(k1_tarski(X0),u1_struct_0(sK0)) | k1_tarski(X0) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(X0))) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.47    inference(resolution,[],[f64,f43])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.20/0.47    inference(resolution,[],[f59,f45])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f56,f31])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 0.20/0.47    inference(resolution,[],[f55,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    v2_tex_2(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_tex_2(X1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f54,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f53,f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X0)) = X0 | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.47    inference(resolution,[],[f36,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK3(X0,X1))) & r1_tarski(sK3(X0,X1),X1) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(rectify,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f51,f33])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    k1_tarski(sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k1_tarski(sK2))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.47    inference(superposition,[],[f35,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    k6_domain_1(u1_struct_0(sK0),sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    r2_hidden(sK2,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (13665)------------------------------
% 0.20/0.47  % (13665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (13665)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (13665)Memory used [KB]: 6140
% 0.20/0.47  % (13665)Time elapsed: 0.012 s
% 0.20/0.47  % (13665)------------------------------
% 0.20/0.47  % (13665)------------------------------
% 0.20/0.47  % (13640)Success in time 0.109 s
%------------------------------------------------------------------------------
