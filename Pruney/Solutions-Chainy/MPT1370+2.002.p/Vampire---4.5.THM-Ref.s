%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:50 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 791 expanded)
%              Number of leaves         :   17 ( 306 expanded)
%              Depth                    :   29
%              Number of atoms          :  612 (8412 expanded)
%              Number of equality atoms :   30 ( 648 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(resolution,[],[f173,f39])).

% (2742)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    & v4_pre_topc(sK3,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & v5_pre_topc(sK2,sK0,sK1)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & v8_pre_topc(sK1)
    & v1_compts_1(sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v5_pre_topc(X2,X0,X1)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & v8_pre_topc(X1)
                & v1_compts_1(X0)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,sK0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & v5_pre_topc(X2,sK0,X1)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(sK0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                & v4_pre_topc(X3,sK0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & v5_pre_topc(X2,sK0,X1)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & v8_pre_topc(X1)
            & v1_compts_1(sK0)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1)
              & v4_pre_topc(X3,sK0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v5_pre_topc(X2,sK0,sK1)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & v8_pre_topc(sK1)
          & v1_compts_1(sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1)
            & v4_pre_topc(X3,sK0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v5_pre_topc(X2,sK0,sK1)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & v8_pre_topc(sK1)
        & v1_compts_1(sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1)
          & v4_pre_topc(X3,sK0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & v5_pre_topc(sK2,sK0,sK1)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & v8_pre_topc(sK1)
      & v1_compts_1(sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1)
        & v4_pre_topc(X3,sK0)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
      & v4_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  & v4_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & v5_pre_topc(X2,X0,X1)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v5_pre_topc(X2,X0,X1)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                       => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).

fof(f173,plain,(
    v2_struct_0(sK1) ),
    inference(resolution,[],[f169,f74])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f49,f69])).

fof(f69,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f54,f67])).

fof(f67,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f55,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f169,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f167,f131])).

fof(f131,plain,(
    v2_compts_1(sK3,sK0) ),
    inference(resolution,[],[f130,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f53,f52])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f130,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(sK3,sK0) ),
    inference(resolution,[],[f129,f108])).

fof(f108,plain,(
    r1_tarski(sK3,k2_struct_0(sK0)) ),
    inference(resolution,[],[f104,f74])).

fof(f104,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | r1_tarski(sK3,k2_struct_0(sK0)) ),
    inference(resolution,[],[f101,f66])).

fof(f101,plain,(
    ! [X8] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X8))
      | r1_tarski(sK3,k2_struct_0(sK0))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X8)) ) ),
    inference(resolution,[],[f97,f74])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | r1_tarski(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | r1_tarski(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f87,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK4(X0,X1,X2),X2)
            & r2_hidden(sK4(X0,X1,X2),X1)
            & m1_subset_1(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X2,X0,X1),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f63,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f129,plain,
    ( ~ r1_tarski(sK3,k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(sK3,sK0) ),
    inference(resolution,[],[f116,f38])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r1_tarski(sK3,k2_struct_0(sK0))
    | v2_compts_1(sK3,sK0) ),
    inference(resolution,[],[f115,f45])).

fof(f45,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f115,plain,
    ( ~ v1_compts_1(sK0)
    | v2_compts_1(sK3,sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ r1_tarski(sK3,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f114,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).

fof(f114,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK0)
      | ~ r1_tarski(sK3,X0)
      | v2_compts_1(sK3,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f113,f74])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(sK3,X0)
      | ~ v2_compts_1(X0,sK0)
      | v2_compts_1(sK3,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f112,f38])).

fof(f112,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_compts_1(sK3,sK0)
      | ~ r1_tarski(sK3,X0)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f107,f37])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(sK3,sK0)
      | ~ r1_tarski(sK3,X0)
      | ~ v2_compts_1(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f106,f69])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_compts_1(sK3,sK0)
      | ~ r1_tarski(sK3,X0)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f105,f69])).

fof(f105,plain,(
    ! [X0] :
      ( v2_compts_1(sK3,sK0)
      | ~ r1_tarski(sK3,X0)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f60,f50])).

fof(f50,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(X2,X0)
      | v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_compts_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_compts_1(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ r1_tarski(X2,X1)
              | ~ v2_compts_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).

% (2737)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f167,plain,
    ( ~ v2_compts_1(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f166,f76])).

fof(f76,plain,(
    ~ v4_pre_topc(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3),sK1) ),
    inference(backward_demodulation,[],[f75,f70])).

fof(f70,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f54,f68])).

fof(f68,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    ~ v4_pre_topc(k7_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(backward_demodulation,[],[f51,f69])).

fof(f51,plain,(
    ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f166,plain,(
    ! [X0] :
      ( v4_pre_topc(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_compts_1(X0,sK0)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f165,f78])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f72,f70])).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f44,f69])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f161,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f161,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),k1_zfmisc_1(k2_struct_0(sK1)))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0) ) ),
    inference(resolution,[],[f160,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK1)
      | v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) ) ),
    inference(resolution,[],[f84,f41])).

fof(f84,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v4_pre_topc(X0,sK1)
      | ~ v2_compts_1(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) ) ),
    inference(resolution,[],[f83,f40])).

fof(f40,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ v2_compts_1(X0,sK1)
      | v4_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f82,f70])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK1)
      | v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(resolution,[],[f59,f46])).

fof(f46,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v8_pre_topc(X0)
      | ~ v2_compts_1(X1,X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v2_compts_1(X1,X0)
          | ~ v8_pre_topc(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_compts_1(X1,X0)
              & v8_pre_topc(X0) )
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).

fof(f160,plain,(
    ! [X0] :
      ( v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | ~ v2_compts_1(X0,sK0)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f159,f78])).

fof(f159,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_compts_1(X0,sK0)
      | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f157,f38])).

fof(f157,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_compts_1(X0,sK0)
      | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(resolution,[],[f138,f41])).

fof(f138,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_compts_1(X0,sK0)
      | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f128,f79])).

fof(f79,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f71,f70])).

fof(f71,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f43,f69])).

fof(f43,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_compts_1(X0,sK0)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f127,f69])).

fof(f127,plain,(
    ! [X0] :
      ( v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_compts_1(X0,sK0)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f126,f69])).

fof(f126,plain,(
    ! [X0] :
      ( v2_compts_1(k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1)
      | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_compts_1(X0,sK0)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f125,f70])).

fof(f125,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_compts_1(X0,sK0)
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f124,f69])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_compts_1(X0,sK0)
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f123,f70])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_compts_1(X0,sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f122,f69])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
      | ~ v2_compts_1(X0,sK0)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f121,f70])).

fof(f121,plain,(
    ! [X0] :
      ( ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(trivial_inequality_removal,[],[f120])).

fof(f120,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_struct_0(sK1)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f119,f77])).

fof(f77,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f73,f70])).

fof(f73,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f47,f69])).

fof(f47,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f119,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f118,f69])).

fof(f118,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(forward_demodulation,[],[f117,f70])).

fof(f117,plain,(
    ! [X0] :
      ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      | ~ v2_compts_1(X0,sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f111,f48])).

fof(f48,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(sK2,X1,X2)
      | k2_struct_0(X2) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2)
      | ~ v2_compts_1(X0,X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2))
      | v2_compts_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2,X0),X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v2_compts_1(X1,X0)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
      | ~ v5_pre_topc(X3,X0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
      | v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
      | ~ l1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
                  | ~ v2_compts_1(X1,X0)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2)
                  | ~ v2_compts_1(X1,X0)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2)
                  | ~ v5_pre_topc(X3,X0,X2)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ( ( v2_compts_1(X1,X0)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) = k2_struct_0(X2)
                      & v5_pre_topc(X3,X0,X2) )
                   => v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_compts_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n023.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 16:55:21 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.45  % (2759)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.18/0.45  % (2743)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.18/0.46  % (2759)Refutation not found, incomplete strategy% (2759)------------------------------
% 0.18/0.46  % (2759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (2759)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.46  
% 0.18/0.46  % (2759)Memory used [KB]: 10618
% 0.18/0.46  % (2759)Time elapsed: 0.013 s
% 0.18/0.46  % (2759)------------------------------
% 0.18/0.46  % (2759)------------------------------
% 0.18/0.46  % (2748)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.18/0.46  % (2743)Refutation not found, incomplete strategy% (2743)------------------------------
% 0.18/0.46  % (2743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (2743)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.46  
% 0.18/0.46  % (2743)Memory used [KB]: 6268
% 0.18/0.46  % (2743)Time elapsed: 0.007 s
% 0.18/0.46  % (2743)------------------------------
% 0.18/0.46  % (2743)------------------------------
% 0.18/0.46  % (2753)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.18/0.47  % (2741)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.18/0.47  % (2745)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.18/0.47  % (2751)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.18/0.48  % (2745)Refutation found. Thanks to Tanya!
% 0.18/0.48  % SZS status Theorem for theBenchmark
% 0.18/0.48  % SZS output start Proof for theBenchmark
% 0.18/0.48  fof(f174,plain,(
% 0.18/0.48    $false),
% 0.18/0.48    inference(resolution,[],[f173,f39])).
% 0.18/0.48  % (2742)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.18/0.48  fof(f39,plain,(
% 0.18/0.48    ~v2_struct_0(sK1)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f33,plain,(
% 0.18/0.48    (((~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) & v4_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(sK2,sK0,sK1) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f32,f31,f30,f29])).
% 0.18/0.48  fof(f29,plain,(
% 0.18/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,X1) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f30,plain,(
% 0.18/0.48    ? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,X1) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,sK1) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f31,plain,(
% 0.18/0.48    ? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(X2,sK0,sK1) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & v5_pre_topc(sK2,sK0,sK1) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & v8_pre_topc(sK1) & v1_compts_1(sK0) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f32,plain,(
% 0.18/0.48    ? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3),sK1) & v4_pre_topc(X3,sK0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) & v4_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f15,plain,(
% 0.18/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.18/0.48    inference(flattening,[],[f14])).
% 0.18/0.48  fof(f14,plain,(
% 0.18/0.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & (v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.18/0.48    inference(ennf_transformation,[],[f13])).
% 0.18/0.48  fof(f13,negated_conjecture,(
% 0.18/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 0.18/0.48    inference(negated_conjecture,[],[f12])).
% 0.18/0.48  fof(f12,conjecture,(
% 0.18/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).
% 0.18/0.48  fof(f173,plain,(
% 0.18/0.48    v2_struct_0(sK1)),
% 0.18/0.48    inference(resolution,[],[f169,f74])).
% 0.18/0.48  fof(f74,plain,(
% 0.18/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.18/0.48    inference(backward_demodulation,[],[f49,f69])).
% 0.18/0.48  fof(f69,plain,(
% 0.18/0.48    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.18/0.48    inference(resolution,[],[f54,f67])).
% 0.18/0.48  fof(f67,plain,(
% 0.18/0.48    l1_struct_0(sK0)),
% 0.18/0.48    inference(resolution,[],[f55,f38])).
% 0.18/0.48  fof(f38,plain,(
% 0.18/0.48    l1_pre_topc(sK0)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f55,plain,(
% 0.18/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f17])).
% 0.18/0.48  fof(f17,plain,(
% 0.18/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f7])).
% 0.18/0.48  fof(f7,axiom,(
% 0.18/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.18/0.48  fof(f54,plain,(
% 0.18/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f16])).
% 0.18/0.48  fof(f16,plain,(
% 0.18/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f6])).
% 0.18/0.48  fof(f6,axiom,(
% 0.18/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.18/0.48  fof(f49,plain,(
% 0.18/0.48    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f169,plain,(
% 0.18/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK1)),
% 0.18/0.48    inference(resolution,[],[f167,f131])).
% 0.18/0.48  fof(f131,plain,(
% 0.18/0.48    v2_compts_1(sK3,sK0)),
% 0.18/0.48    inference(resolution,[],[f130,f66])).
% 0.18/0.48  fof(f66,plain,(
% 0.18/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.18/0.48    inference(forward_demodulation,[],[f53,f52])).
% 0.18/0.48  fof(f52,plain,(
% 0.18/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.18/0.48    inference(cnf_transformation,[],[f1])).
% 0.18/0.48  fof(f1,axiom,(
% 0.18/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.18/0.48  fof(f53,plain,(
% 0.18/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f2])).
% 0.18/0.48  fof(f2,axiom,(
% 0.18/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.18/0.48  fof(f130,plain,(
% 0.18/0.48    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(sK3,sK0)),
% 0.18/0.48    inference(resolution,[],[f129,f108])).
% 0.18/0.48  fof(f108,plain,(
% 0.18/0.48    r1_tarski(sK3,k2_struct_0(sK0))),
% 0.18/0.48    inference(resolution,[],[f104,f74])).
% 0.18/0.48  fof(f104,plain,(
% 0.18/0.48    ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(sK3,k2_struct_0(sK0))),
% 0.18/0.48    inference(resolution,[],[f101,f66])).
% 0.18/0.48  fof(f101,plain,(
% 0.18/0.48    ( ! [X8] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(X8)) | r1_tarski(sK3,k2_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(X8))) )),
% 0.18/0.48    inference(resolution,[],[f97,f74])).
% 0.18/0.48  fof(f97,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_tarski(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.18/0.48    inference(duplicate_literal_removal,[],[f95])).
% 0.18/0.48  fof(f95,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | r1_tarski(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) )),
% 0.18/0.48    inference(resolution,[],[f87,f64])).
% 0.18/0.48  fof(f64,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f36])).
% 0.18/0.48  fof(f36,plain,(
% 0.18/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f27,f35])).
% 0.18/0.48  fof(f35,plain,(
% 0.18/0.48    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK4(X0,X1,X2),X2) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),X0)))),
% 0.18/0.48    introduced(choice_axiom,[])).
% 0.18/0.48  fof(f27,plain,(
% 0.18/0.48    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.48    inference(flattening,[],[f26])).
% 0.18/0.48  fof(f26,plain,(
% 0.18/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.48    inference(ennf_transformation,[],[f4])).
% 0.18/0.48  fof(f4,axiom,(
% 0.18/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.18/0.48  fof(f87,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(sK4(X2,X0,X1),X3) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X3))) )),
% 0.18/0.48    inference(resolution,[],[f63,f61])).
% 0.18/0.48  fof(f61,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f25])).
% 0.18/0.48  fof(f25,plain,(
% 0.18/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.48    inference(ennf_transformation,[],[f3])).
% 0.18/0.48  fof(f3,axiom,(
% 0.18/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.18/0.48  fof(f63,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f36])).
% 0.18/0.48  fof(f129,plain,(
% 0.18/0.48    ~r1_tarski(sK3,k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(sK3,sK0)),
% 0.18/0.48    inference(resolution,[],[f116,f38])).
% 0.18/0.48  fof(f116,plain,(
% 0.18/0.48    ~l1_pre_topc(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK3,k2_struct_0(sK0)) | v2_compts_1(sK3,sK0)),
% 0.18/0.48    inference(resolution,[],[f115,f45])).
% 0.18/0.48  fof(f45,plain,(
% 0.18/0.48    v1_compts_1(sK0)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f115,plain,(
% 0.18/0.48    ~v1_compts_1(sK0) | v2_compts_1(sK3,sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK3,k2_struct_0(sK0)) | ~l1_pre_topc(sK0)),
% 0.18/0.48    inference(resolution,[],[f114,f56])).
% 0.18/0.48  fof(f56,plain,(
% 0.18/0.48    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f34])).
% 0.18/0.48  fof(f34,plain,(
% 0.18/0.48    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 0.18/0.48    inference(nnf_transformation,[],[f18])).
% 0.18/0.48  fof(f18,plain,(
% 0.18/0.48    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f8])).
% 0.18/0.48  fof(f8,axiom,(
% 0.18/0.48    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_compts_1)).
% 0.18/0.48  fof(f114,plain,(
% 0.18/0.48    ( ! [X0] : (~v2_compts_1(X0,sK0) | ~r1_tarski(sK3,X0) | v2_compts_1(sK3,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.18/0.48    inference(resolution,[],[f113,f74])).
% 0.18/0.48  fof(f113,plain,(
% 0.18/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(sK3,X0) | ~v2_compts_1(X0,sK0) | v2_compts_1(sK3,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.18/0.48    inference(resolution,[],[f112,f38])).
% 0.18/0.48  fof(f112,plain,(
% 0.18/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | v2_compts_1(sK3,sK0) | ~r1_tarski(sK3,X0) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.18/0.48    inference(resolution,[],[f107,f37])).
% 0.18/0.48  fof(f37,plain,(
% 0.18/0.48    v2_pre_topc(sK0)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f107,plain,(
% 0.18/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(sK3,sK0) | ~r1_tarski(sK3,X0) | ~v2_compts_1(X0,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.18/0.48    inference(forward_demodulation,[],[f106,f69])).
% 0.18/0.48  fof(f106,plain,(
% 0.18/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(sK3,sK0) | ~r1_tarski(sK3,X0) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f105,f69])).
% 0.18/0.48  fof(f105,plain,(
% 0.18/0.48    ( ! [X0] : (v2_compts_1(sK3,sK0) | ~r1_tarski(sK3,X0) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.18/0.48    inference(resolution,[],[f60,f50])).
% 0.18/0.48  fof(f50,plain,(
% 0.18/0.48    v4_pre_topc(sK3,sK0)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f60,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~v4_pre_topc(X2,X0) | v2_compts_1(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f24])).
% 0.18/0.48  fof(f24,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (! [X2] : (v2_compts_1(X2,X0) | ~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.18/0.48    inference(flattening,[],[f23])).
% 0.18/0.48  fof(f23,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) | (~v4_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~v2_compts_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.18/0.48    inference(ennf_transformation,[],[f10])).
% 0.18/0.48  fof(f10,axiom,(
% 0.18/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_compts_1)).
% 0.18/0.48  % (2737)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.18/0.48  fof(f167,plain,(
% 0.18/0.48    ~v2_compts_1(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK1)),
% 0.18/0.48    inference(resolution,[],[f166,f76])).
% 0.18/0.48  fof(f76,plain,(
% 0.18/0.48    ~v4_pre_topc(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3),sK1)),
% 0.18/0.48    inference(backward_demodulation,[],[f75,f70])).
% 0.18/0.48  fof(f70,plain,(
% 0.18/0.48    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.18/0.48    inference(resolution,[],[f54,f68])).
% 0.18/0.48  fof(f68,plain,(
% 0.18/0.48    l1_struct_0(sK1)),
% 0.18/0.48    inference(resolution,[],[f55,f41])).
% 0.18/0.48  fof(f41,plain,(
% 0.18/0.48    l1_pre_topc(sK1)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f75,plain,(
% 0.18/0.48    ~v4_pre_topc(k7_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)),
% 0.18/0.48    inference(backward_demodulation,[],[f51,f69])).
% 0.18/0.48  fof(f51,plain,(
% 0.18/0.48    ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f166,plain,(
% 0.18/0.48    ( ! [X0] : (v4_pre_topc(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_compts_1(X0,sK0) | v2_struct_0(sK1)) )),
% 0.18/0.48    inference(resolution,[],[f165,f78])).
% 0.18/0.48  fof(f78,plain,(
% 0.18/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.18/0.48    inference(backward_demodulation,[],[f72,f70])).
% 0.18/0.48  fof(f72,plain,(
% 0.18/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.18/0.48    inference(backward_demodulation,[],[f44,f69])).
% 0.18/0.48  fof(f44,plain,(
% 0.18/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f165,plain,(
% 0.18/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0) | v2_struct_0(sK1)) )),
% 0.18/0.48    inference(resolution,[],[f161,f65])).
% 0.18/0.48  fof(f65,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.48    inference(cnf_transformation,[],[f28])).
% 0.18/0.48  fof(f28,plain,(
% 0.18/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.48    inference(ennf_transformation,[],[f5])).
% 0.18/0.48  fof(f5,axiom,(
% 0.18/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.18/0.48  fof(f161,plain,(
% 0.18/0.48    ( ! [X0] : (~m1_subset_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),k1_zfmisc_1(k2_struct_0(sK1))) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0)) )),
% 0.18/0.48    inference(resolution,[],[f160,f85])).
% 0.18/0.48  fof(f85,plain,(
% 0.18/0.48    ( ! [X0] : (~v2_compts_1(X0,sK1) | v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))) )),
% 0.18/0.48    inference(resolution,[],[f84,f41])).
% 0.18/0.48  fof(f84,plain,(
% 0.18/0.48    ( ! [X0] : (~l1_pre_topc(sK1) | v4_pre_topc(X0,sK1) | ~v2_compts_1(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))) )),
% 0.18/0.48    inference(resolution,[],[f83,f40])).
% 0.18/0.48  fof(f40,plain,(
% 0.18/0.48    v2_pre_topc(sK1)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f83,plain,(
% 0.18/0.48    ( ! [X0] : (~v2_pre_topc(sK1) | ~v2_compts_1(X0,sK1) | v4_pre_topc(X0,sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))) )),
% 0.18/0.48    inference(forward_demodulation,[],[f82,f70])).
% 0.18/0.48  fof(f82,plain,(
% 0.18/0.48    ( ! [X0] : (~v2_compts_1(X0,sK1) | v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 0.18/0.48    inference(resolution,[],[f59,f46])).
% 0.18/0.48  fof(f46,plain,(
% 0.18/0.48    v8_pre_topc(sK1)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f59,plain,(
% 0.18/0.48    ( ! [X0,X1] : (~v8_pre_topc(X0) | ~v2_compts_1(X1,X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f22])).
% 0.18/0.48  fof(f22,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v2_compts_1(X1,X0) | ~v8_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.18/0.48    inference(flattening,[],[f21])).
% 0.18/0.48  fof(f21,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | (~v2_compts_1(X1,X0) | ~v8_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.18/0.48    inference(ennf_transformation,[],[f9])).
% 0.18/0.48  fof(f9,axiom,(
% 0.18/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_compts_1(X1,X0) & v8_pre_topc(X0)) => v4_pre_topc(X1,X0))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_compts_1)).
% 0.18/0.48  fof(f160,plain,(
% 0.18/0.48    ( ! [X0] : (v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | ~v2_compts_1(X0,sK0) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.18/0.48    inference(resolution,[],[f159,f78])).
% 0.18/0.48  fof(f159,plain,(
% 0.18/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_compts_1(X0,sK0) | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.18/0.48    inference(resolution,[],[f157,f38])).
% 0.18/0.48  fof(f157,plain,(
% 0.18/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_compts_1(X0,sK0) | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.18/0.48    inference(resolution,[],[f138,f41])).
% 0.18/0.48  fof(f138,plain,(
% 0.18/0.48    ( ! [X0] : (~l1_pre_topc(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_compts_1(X0,sK0) | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(resolution,[],[f128,f79])).
% 0.18/0.48  fof(f79,plain,(
% 0.18/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.18/0.48    inference(backward_demodulation,[],[f71,f70])).
% 0.18/0.48  fof(f71,plain,(
% 0.18/0.48    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.18/0.48    inference(backward_demodulation,[],[f43,f69])).
% 0.18/0.48  fof(f43,plain,(
% 0.18/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f128,plain,(
% 0.18/0.48    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_compts_1(X0,sK0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f127,f69])).
% 0.18/0.48  fof(f127,plain,(
% 0.18/0.48    ( ! [X0] : (v2_compts_1(k7_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_compts_1(X0,sK0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f126,f69])).
% 0.18/0.48  fof(f126,plain,(
% 0.18/0.48    ( ! [X0] : (v2_compts_1(k7_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,X0),sK1) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_compts_1(X0,sK0) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f125,f70])).
% 0.18/0.48  fof(f125,plain,(
% 0.18/0.48    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_compts_1(X0,sK0) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f124,f69])).
% 0.18/0.48  fof(f124,plain,(
% 0.18/0.48    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_compts_1(X0,sK0) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f123,f70])).
% 0.18/0.48  fof(f123,plain,(
% 0.18/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_compts_1(X0,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f122,f69])).
% 0.18/0.48  fof(f122,plain,(
% 0.18/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_compts_1(X0,sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f121,f70])).
% 0.18/0.48  fof(f121,plain,(
% 0.18/0.48    ( ! [X0] : (~v2_compts_1(X0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(trivial_inequality_removal,[],[f120])).
% 0.18/0.48  fof(f120,plain,(
% 0.18/0.48    ( ! [X0] : (k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f119,f77])).
% 0.18/0.48  fof(f77,plain,(
% 0.18/0.48    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.18/0.48    inference(backward_demodulation,[],[f73,f70])).
% 0.18/0.48  fof(f73,plain,(
% 0.18/0.48    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.18/0.48    inference(backward_demodulation,[],[f47,f69])).
% 0.18/0.48  fof(f47,plain,(
% 0.18/0.48    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f119,plain,(
% 0.18/0.48    ( ! [X0] : (k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f118,f69])).
% 0.18/0.48  fof(f118,plain,(
% 0.18/0.48    ( ! [X0] : (k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(forward_demodulation,[],[f117,f70])).
% 0.18/0.48  fof(f117,plain,(
% 0.18/0.48    ( ! [X0] : (k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_compts_1(X0,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v2_compts_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.18/0.48    inference(resolution,[],[f111,f48])).
% 0.18/0.48  fof(f48,plain,(
% 0.18/0.48    v5_pre_topc(sK2,sK0,sK1)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f111,plain,(
% 0.18/0.48    ( ! [X2,X0,X1] : (~v5_pre_topc(sK2,X1,X2) | k2_struct_0(X2) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2) | ~v2_compts_1(X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X2)) | v2_compts_1(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),sK2,X0),X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 0.18/0.48    inference(resolution,[],[f58,f42])).
% 0.18/0.48  fof(f42,plain,(
% 0.18/0.48    v1_funct_1(sK2)),
% 0.18/0.48    inference(cnf_transformation,[],[f33])).
% 0.18/0.48  fof(f58,plain,(
% 0.18/0.48    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | ~l1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.48    inference(cnf_transformation,[],[f20])).
% 0.18/0.48  fof(f20,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | ~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.48    inference(flattening,[],[f19])).
% 0.18/0.48  fof(f19,plain,(
% 0.18/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2) | (~v2_compts_1(X1,X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) != k2_struct_0(X2) | ~v5_pre_topc(X3,X0,X2))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.48    inference(ennf_transformation,[],[f11])).
% 0.18/0.48  fof(f11,axiom,(
% 0.18/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((l1_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X2)) & v1_funct_1(X3)) => ((v2_compts_1(X1,X0) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3) = k2_struct_0(X2) & v5_pre_topc(X3,X0,X2)) => v2_compts_1(k7_relset_1(u1_struct_0(X0),u1_struct_0(X2),X3,X1),X2))))))),
% 0.18/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_compts_1)).
% 0.18/0.48  % SZS output end Proof for theBenchmark
% 0.18/0.48  % (2745)------------------------------
% 0.18/0.48  % (2745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (2745)Termination reason: Refutation
% 0.18/0.48  
% 0.18/0.48  % (2745)Memory used [KB]: 1791
% 0.18/0.48  % (2745)Time elapsed: 0.101 s
% 0.18/0.48  % (2745)------------------------------
% 0.18/0.48  % (2745)------------------------------
% 0.18/0.48  % (2752)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.18/0.48  % (2735)Success in time 0.146 s
%------------------------------------------------------------------------------
