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
% DateTime   : Thu Dec  3 13:09:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 298 expanded)
%              Number of leaves         :    8 (  82 expanded)
%              Depth                    :   23
%              Number of atoms          :  274 (1275 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(subsumption_resolution,[],[f135,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f32,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f135,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f130,f38])).

fof(f130,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | ~ r1_tarski(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f120,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK3(X3,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(sK1,X0)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f78,f38])).

fof(f78,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r1_tarski(X7,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X3)
      | ~ r1_tarski(sK1,X5)
      | ~ r1_tarski(X3,X4)
      | ~ r2_hidden(sK3(X4,k2_pre_topc(sK0,sK1)),X7) ) ),
    inference(resolution,[],[f76,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(sK3(X0,X1),X2) ) ),
    inference(resolution,[],[f30,f32])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X3,X0)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f74,f24])).

fof(f24,plain,(
    ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11,f10])).

fof(f10,plain,
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

fof(f11,plain,
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

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X3,X0)
      | ~ r1_tarski(X2,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(sK1,X3)
      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f62,f31])).

fof(f62,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X7)
      | ~ r1_tarski(X4,X5)
      | ~ r1_tarski(X5,X3)
      | ~ r1_tarski(X6,X4)
      | ~ r1_tarski(X3,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X7,X6) ) ),
    inference(resolution,[],[f53,f30])).

fof(f53,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X5)
      | ~ r1_tarski(X3,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X4,X2)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X5,X4) ) ),
    inference(resolution,[],[f44,f30])).

fof(f44,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X3)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X1,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f42,f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X1)
      | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f40,f30])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X0)
      | ~ r1_tarski(X0,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f39,f24])).

fof(f120,plain,(
    ! [X3] :
      ( r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X3,sK1)
      | ~ r1_tarski(sK1,X3) ) ),
    inference(resolution,[],[f115,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f52,f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(sK1,X0)
      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f44,f31])).

fof(f115,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f114,f35])).

fof(f35,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f114,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(sK1,u1_struct_0(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(sK1,u1_struct_0(sK0))
      | r1_tarski(sK1,X0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f110,f31])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(sK1,X0),X1)
      | r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X1,u1_struct_0(sK0))
      | r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f109,f30])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(sK3(sK1,X0),X1)
      | ~ r1_tarski(X1,u1_struct_0(sK0))
      | r1_tarski(sK1,X0)
      | ~ r2_hidden(sK3(sK1,X0),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f108,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(sK3(sK1,X0),X1)
      | ~ r1_tarski(X1,u1_struct_0(sK0))
      | r1_tarski(sK1,X0)
      | ~ r2_hidden(sK3(sK1,X0),u1_struct_0(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f107,f23])).

fof(f107,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(sK3(sK1,X0),X1)
      | ~ r1_tarski(X1,u1_struct_0(sK0))
      | r1_tarski(sK1,X0)
      | ~ r2_hidden(sK3(sK1,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(sK3(sK1,X0),X1)
      | ~ r1_tarski(X1,u1_struct_0(sK0))
      | r1_tarski(sK1,X0)
      | r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(sK3(sK1,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f93,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,sK2(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).

fof(f15,plain,(
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
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
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

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,sK2(sK0,sK1,sK3(X0,X1)))
      | r2_hidden(sK3(X0,X1),k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(sK3(X0,X1),X2)
      | ~ r1_tarski(X2,u1_struct_0(sK0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f92,f31])).

fof(f92,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | r2_hidden(X2,k2_pre_topc(sK0,sK1))
      | ~ r1_tarski(X3,sK2(sK0,sK1,X2))
      | ~ r2_hidden(X2,X4)
      | ~ r1_tarski(X4,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f89,f30])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,sK2(sK0,sK1,X0)) ) ),
    inference(resolution,[],[f88,f23])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k2_pre_topc(sK0,X1))
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X2,sK2(sK0,X1,X0)) ) ),
    inference(resolution,[],[f87,f30])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2(sK0,X1,X0))
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_pre_topc(sK0,X1)) ) ),
    inference(resolution,[],[f29,f22])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,sK2(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:02:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (30849)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.47  % (30842)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (30857)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (30842)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f135,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.49    inference(resolution,[],[f32,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(rectify,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ~r1_tarski(sK1,sK1)),
% 0.21/0.49    inference(resolution,[],[f130,f38])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X3] : (~r1_tarski(X3,sK1) | ~r1_tarski(sK1,X3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f120,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK3(X3,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) | ~r1_tarski(X1,X2) | ~r1_tarski(sK1,X0) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f78,f38])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X6,X4,X7,X5,X3] : (~r1_tarski(X7,k2_pre_topc(sK0,sK1)) | ~r1_tarski(X5,X6) | ~r1_tarski(X6,X3) | ~r1_tarski(sK1,X5) | ~r1_tarski(X3,X4) | ~r2_hidden(sK3(X4,k2_pre_topc(sK0,sK1)),X7)) )),
% 0.21/0.49    inference(resolution,[],[f76,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r2_hidden(sK3(X0,X1),X2)) )),
% 0.21/0.49    inference(resolution,[],[f30,f32])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k2_pre_topc(sK0,sK1)) | ~r1_tarski(X1,X2) | ~r1_tarski(X3,X0) | ~r1_tarski(X0,X1) | ~r1_tarski(sK1,X3)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f74,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    (~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11,f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r1_tarski(X1,k2_pre_topc(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(X1,k2_pre_topc(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X1] : (~r1_tarski(X1,k2_pre_topc(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (~r1_tarski(X1,k2_pre_topc(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,k2_pre_topc(sK0,sK1)) | ~r1_tarski(sK1,X3) | r1_tarski(sK1,k2_pre_topc(sK0,sK1))) )),
% 0.21/0.49    inference(resolution,[],[f62,f31])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X6,X4,X7,X5,X3] : (~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X7) | ~r1_tarski(X4,X5) | ~r1_tarski(X5,X3) | ~r1_tarski(X6,X4) | ~r1_tarski(X3,k2_pre_topc(sK0,sK1)) | ~r1_tarski(X7,X6)) )),
% 0.21/0.49    inference(resolution,[],[f53,f30])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X4,X2,X5,X3] : (~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X5) | ~r1_tarski(X3,k2_pre_topc(sK0,sK1)) | ~r1_tarski(X4,X2) | ~r1_tarski(X2,X3) | ~r1_tarski(X5,X4)) )),
% 0.21/0.49    inference(resolution,[],[f44,f30])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X3,X1] : (~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X3) | ~r1_tarski(X2,X1) | ~r1_tarski(X1,k2_pre_topc(sK0,sK1)) | ~r1_tarski(X3,X2)) )),
% 0.21/0.49    inference(resolution,[],[f42,f30])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X1) | ~r1_tarski(X0,k2_pre_topc(sK0,sK1)) | ~r1_tarski(X1,X0)) )),
% 0.21/0.49    inference(resolution,[],[f40,f30])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),X0) | ~r1_tarski(X0,k2_pre_topc(sK0,sK1))) )),
% 0.21/0.49    inference(resolution,[],[f39,f24])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X3] : (r2_hidden(sK3(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) | ~r1_tarski(X3,sK1) | ~r1_tarski(sK1,X3)) )),
% 0.21/0.49    inference(resolution,[],[f115,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X1,k2_pre_topc(sK0,sK1)) | ~r1_tarski(X0,X1) | ~r1_tarski(sK1,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f52,f24])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,k2_pre_topc(sK0,sK1)) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k2_pre_topc(sK0,sK1))) )),
% 0.21/0.49    inference(resolution,[],[f44,f31])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(sK1,X0) | r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f114,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f33,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1)) | ~r1_tarski(sK1,u1_struct_0(sK0)) | r1_tarski(sK1,X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f112])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1)) | ~r1_tarski(sK1,u1_struct_0(sK0)) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) )),
% 0.21/0.49    inference(resolution,[],[f110,f31])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(sK3(sK1,X0),X1) | r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1)) | ~r1_tarski(X1,u1_struct_0(sK0)) | r1_tarski(sK1,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f30])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1)) | ~r2_hidden(sK3(sK1,X0),X1) | ~r1_tarski(X1,u1_struct_0(sK0)) | r1_tarski(sK1,X0) | ~r2_hidden(sK3(sK1,X0),u1_struct_0(sK0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f108,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1)) | ~r2_hidden(sK3(sK1,X0),X1) | ~r1_tarski(X1,u1_struct_0(sK0)) | r1_tarski(sK1,X0) | ~r2_hidden(sK3(sK1,X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f107,f23])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1)) | ~r2_hidden(sK3(sK1,X0),X1) | ~r1_tarski(X1,u1_struct_0(sK0)) | r1_tarski(sK1,X0) | ~r2_hidden(sK3(sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f105])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1)) | ~r2_hidden(sK3(sK1,X0),X1) | ~r1_tarski(X1,u1_struct_0(sK0)) | r1_tarski(sK1,X0) | r2_hidden(sK3(sK1,X0),k2_pre_topc(sK0,sK1)) | ~r2_hidden(sK3(sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 0.21/0.49    inference(resolution,[],[f93,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(X1,sK2(X0,X1,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (~r2_hidden(X2,sK2(X0,X1,X2)) & r1_tarski(X1,sK2(X0,X1,X2)) & v4_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X2,sK2(X0,X1,X2)) & r1_tarski(X1,sK2(X0,X1,X2)) & v4_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(rectify,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : ((r2_hidden(X2,X3) | (~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (r2_hidden(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) => r2_hidden(X2,X3)))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,sK2(sK0,sK1,sK3(X0,X1))) | r2_hidden(sK3(X0,X1),k2_pre_topc(sK0,sK1)) | ~r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X2,u1_struct_0(sK0)) | r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(resolution,[],[f92,f31])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X4,X2,X3] : (~r2_hidden(X2,X3) | r2_hidden(X2,k2_pre_topc(sK0,sK1)) | ~r1_tarski(X3,sK2(sK0,sK1,X2)) | ~r2_hidden(X2,X4) | ~r1_tarski(X4,u1_struct_0(sK0))) )),
% 0.21/0.49    inference(resolution,[],[f89,f30])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(X0,k2_pre_topc(sK0,sK1)) | ~r2_hidden(X0,X1) | ~r1_tarski(X1,sK2(sK0,sK1,X0))) )),
% 0.21/0.49    inference(resolution,[],[f88,f23])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(X0,k2_pre_topc(sK0,X1)) | ~r2_hidden(X0,X2) | ~r1_tarski(X2,sK2(sK0,X1,X0))) )),
% 0.21/0.49    inference(resolution,[],[f87,f30])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,sK2(sK0,X1,X0)) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,k2_pre_topc(sK0,X1))) )),
% 0.21/0.49    inference(resolution,[],[f29,f22])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r2_hidden(X2,sK2(X0,X1,X2)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,k2_pre_topc(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (30842)------------------------------
% 0.21/0.49  % (30842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30842)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (30842)Memory used [KB]: 5373
% 0.21/0.49  % (30842)Time elapsed: 0.057 s
% 0.21/0.49  % (30842)------------------------------
% 0.21/0.49  % (30842)------------------------------
% 0.21/0.49  % (30841)Success in time 0.123 s
%------------------------------------------------------------------------------
