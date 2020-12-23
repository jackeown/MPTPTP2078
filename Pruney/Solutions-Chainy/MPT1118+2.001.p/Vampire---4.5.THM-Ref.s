%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 834 expanded)
%              Number of leaves         :   10 ( 300 expanded)
%              Depth                    :   12
%              Number of atoms          :  223 (4341 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(subsumption_resolution,[],[f124,f105])).

fof(f105,plain,(
    r2_hidden(sK4(sK1,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),sK2) ),
    inference(unit_resulting_resolution,[],[f30,f85,f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f85,plain,(
    r2_hidden(sK4(sK1,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),sK1) ),
    inference(unit_resulting_resolution,[],[f71,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,(
    ~ r1_tarski(sK1,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f27,f28,f50,f42,f54,f51,f52,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_tarski(X1,X4)
      | r2_hidden(X2,X4)
      | ~ v4_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( ~ r2_hidden(X2,sK3(X0,X1,X2))
                    & r1_tarski(X1,sK3(X0,X1,X2))
                    & v4_pre_topc(sK3(X0,X1,X2),X0)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( r2_hidden(X2,X4)
                      | ~ r1_tarski(X1,X4)
                      | ~ v4_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ r2_hidden(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X2,X3)
          & r1_tarski(X1,X3)
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(X2,sK3(X0,X1,X2))
        & r1_tarski(X1,sK3(X0,X1,X2))
        & v4_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f52,plain,(
    ~ r2_hidden(sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f27,f29,f50,f43,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK3(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ~ r2_hidden(sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f31,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X1,X2)
                 => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f51,plain,(
    m1_subset_1(sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f27,f29,f50,f43,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    v4_pre_topc(sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),sK0) ),
    inference(unit_resulting_resolution,[],[f27,f29,f50,f43,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X0))
      | v4_pre_topc(sK3(X0,X1,X2),X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,(
    r2_hidden(sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f31,f40])).

fof(f50,plain,(
    r2_hidden(sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f44,f42,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f44,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f27,f28,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f124,plain,(
    ~ r2_hidden(sK4(sK1,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),sK2) ),
    inference(unit_resulting_resolution,[],[f53,f84,f39])).

fof(f84,plain,(
    ~ r2_hidden(sK4(sK1,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f71,f41])).

fof(f53,plain,(
    r1_tarski(sK2,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) ),
    inference(unit_resulting_resolution,[],[f27,f29,f50,f43,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(X0))
      | r1_tarski(X1,sK3(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:43:39 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (13117)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.45  % (13125)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.47  % (13126)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.47  % (13120)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.47  % (13115)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.47  % (13118)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.47  % (13125)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f124,f105])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    r2_hidden(sK4(sK1,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),sK2)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f30,f85,f39])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(rectify,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(nnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    r2_hidden(sK4(sK1,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),sK1)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f71,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    ~r1_tarski(sK1,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f27,f28,f50,f42,f54,f51,f52,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X4,X2,X0,X1] : (~r1_tarski(X1,X4) | r2_hidden(X2,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (~r2_hidden(X2,sK3(X0,X1,X2)) & r1_tarski(X1,sK3(X0,X1,X2)) & v4_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(X2,sK3(X0,X1,X2)) & r1_tarski(X1,sK3(X0,X1,X2)) & v4_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X2,X4) | ~r1_tarski(X1,X4) | ~v4_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(rectify,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (~r2_hidden(X2,X3) & r1_tarski(X1,X3) & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (r2_hidden(X2,X3) | ~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : ((r2_hidden(X2,X3) | (~r1_tarski(X1,X3) | ~v4_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (r2_hidden(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X3) & v4_pre_topc(X3,X0)) => r2_hidden(X2,X3)))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_pre_topc)).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ~r2_hidden(sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f27,f29,f50,f43,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,sK3(X0,X1,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~r2_hidden(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ~r2_hidden(sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK2))),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f31,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f26])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ((~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X2] : (~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f5])).
% 0.22/0.47  fof(f5,conjecture,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    m1_subset_1(sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f27,f29,f50,f43,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    v4_pre_topc(sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),sK0)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f27,f29,f50,f43,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X0)) | v4_pre_topc(sK3(X0,X1,X2),X0) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    r2_hidden(sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,sK1))),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f31,f40])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    r2_hidden(sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),u1_struct_0(sK0))),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f44,f42,f37])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f27,f28,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    l1_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    r1_tarski(sK1,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    ~r2_hidden(sK4(sK1,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),sK2)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f53,f84,f39])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    ~r2_hidden(sK4(sK1,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f71,f41])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    r1_tarski(sK2,sK3(sK0,sK2,sK4(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f27,f29,f50,f43,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(X0)) | r1_tarski(X1,sK3(X0,X1,X2)) | r2_hidden(X2,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (13125)------------------------------
% 0.22/0.47  % (13125)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (13125)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (13125)Memory used [KB]: 5500
% 0.22/0.47  % (13125)Time elapsed: 0.062 s
% 0.22/0.47  % (13125)------------------------------
% 0.22/0.47  % (13125)------------------------------
% 0.22/0.47  % (13110)Success in time 0.109 s
%------------------------------------------------------------------------------
