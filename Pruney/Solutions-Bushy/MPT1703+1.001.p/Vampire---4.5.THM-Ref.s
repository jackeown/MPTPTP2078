%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1703+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:22 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  204 (18879 expanded)
%              Number of leaves         :   16 (5872 expanded)
%              Depth                    :   79
%              Number of atoms          :  900 (156266 expanded)
%              Number of equality atoms :  161 (21001 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f622,plain,(
    $false ),
    inference(subsumption_resolution,[],[f621,f105])).

fof(f105,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f104,f70])).

fof(f70,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f67,f39])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0) )
    & ( m1_pre_topc(sK2,sK0)
      | m1_pre_topc(sK1,sK0) )
    & sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) )
                & ( m1_pre_topc(X2,X0)
                  | m1_pre_topc(X1,X0) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ m1_pre_topc(X1,sK0) )
              & ( m1_pre_topc(X2,sK0)
                | m1_pre_topc(X1,sK0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK0)
              | ~ m1_pre_topc(X1,sK0) )
            & ( m1_pre_topc(X2,sK0)
              | m1_pre_topc(X1,sK0) )
            & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK0)
            | ~ m1_pre_topc(sK1,sK0) )
          & ( m1_pre_topc(X2,sK0)
            | m1_pre_topc(sK1,sK0) )
          & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK1
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK0)
          | ~ m1_pre_topc(sK1,sK0) )
        & ( m1_pre_topc(X2,sK0)
          | m1_pre_topc(sK1,sK0) )
        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK1
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(sK1,sK0) )
      & ( m1_pre_topc(sK2,sK0)
        | m1_pre_topc(sK1,sK0) )
      & sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ m1_pre_topc(X1,X0) )
              & ( m1_pre_topc(X2,X0)
                | m1_pre_topc(X1,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ m1_pre_topc(X1,X0) )
              & ( m1_pre_topc(X2,X0)
                | m1_pre_topc(X1,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_pre_topc(X1,X0)
              <~> m1_pre_topc(X2,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m1_pre_topc(X1,X0)
              <~> m1_pre_topc(X2,X0) )
              & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
                 => ( m1_pre_topc(X1,X0)
                  <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f104,plain,(
    r1_tarski(k2_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f103,f69])).

fof(f69,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f67,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f103,plain,(
    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f98,f37])).

fof(f98,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f95,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f49,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
                & ( ( sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK4(X0,X1),k2_struct_0(X1))
                    & r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
                    & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X5),k2_struct_0(X1)) = X5
                          & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X0))
                          & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,u1_pre_topc(X1)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & r2_hidden(X4,u1_pre_topc(X0))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,u1_pre_topc(X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK3(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X0))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK3(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK4(X0,X1),k2_struct_0(X1))
        & r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X4] :
                        ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                        & r2_hidden(X4,u1_pre_topc(X0))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X7] :
                            ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
                            & r2_hidden(X7,u1_pre_topc(X0))
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f95,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( m1_pre_topc(sK1,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f93,f42])).

fof(f42,plain,(
    sK1 = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f92,f37])).

fof(f92,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f61,f43])).

fof(f43,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f621,plain,(
    ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f620,f69])).

fof(f620,plain,(
    ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f619,f37])).

fof(f619,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f618,f96])).

fof(f96,plain,(
    ~ m1_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f95,f44])).

fof(f44,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f618,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f617,f209])).

fof(f209,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(X0))
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f208,f118])).

fof(f118,plain,(
    u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,
    ( sK1 != sK1
    | u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(superposition,[],[f114,f42])).

fof(f114,plain,(
    ! [X6,X5] :
      ( sK1 != g1_pre_topc(X5,X6)
      | u1_struct_0(sK1) = X5 ) ),
    inference(forward_demodulation,[],[f112,f81])).

fof(f81,plain,(
    sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f79,f39])).

fof(f79,plain,
    ( sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f48,f74])).

fof(f74,plain,(
    v1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f73,f41])).

fof(f41,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,
    ( v1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f72,f42])).

fof(f72,plain,(
    ! [X0] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f62,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f112,plain,(
    ! [X6,X5] :
      ( u1_struct_0(sK1) = X5
      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X5,X6) ) ),
    inference(resolution,[],[f108,f39])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f64,f47])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f208,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(X0))
      | m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f207,f71])).

fof(f71,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f67,f41])).

fof(f207,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_pre_topc(sK2,X0)
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f206,f41])).

fof(f206,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_pre_topc(sK2,X0)
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X0))
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f54,f118])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | m1_pre_topc(X1,X0)
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f617,plain,(
    ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f616,f566])).

fof(f566,plain,(
    r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f565,f105])).

fof(f565,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f564,f69])).

fof(f564,plain,
    ( r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f563,f37])).

fof(f563,plain,
    ( r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f562,f96])).

fof(f562,plain,
    ( r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f561,f209])).

fof(f561,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f560,f334])).

fof(f334,plain,
    ( m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f333,f143])).

fof(f143,plain,(
    u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
    inference(trivial_inequality_removal,[],[f141])).

fof(f141,plain,
    ( sK1 != sK1
    | u1_pre_topc(sK2) = u1_pre_topc(sK1) ),
    inference(superposition,[],[f137,f81])).

fof(f137,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != sK1
      | u1_pre_topc(sK2) = X1 ) ),
    inference(forward_demodulation,[],[f133,f119])).

fof(f119,plain,(
    sK1 = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) ),
    inference(superposition,[],[f42,f118])).

fof(f133,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
      | u1_pre_topc(sK2) = X1 ) ),
    inference(resolution,[],[f125,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f125,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subsumption_resolution,[],[f122,f41])).

fof(f122,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK2) ),
    inference(superposition,[],[f47,f118])).

fof(f333,plain,
    ( m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f332,f105])).

fof(f332,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK2)) ),
    inference(forward_demodulation,[],[f331,f118])).

fof(f331,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f330,f96])).

fof(f330,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f326,f41])).

fof(f326,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,sK0) ),
    inference(superposition,[],[f318,f71])).

fof(f318,plain,(
    ! [X3] :
      ( ~ r1_tarski(k2_struct_0(X3),u1_struct_0(sK0))
      | m1_subset_1(sK4(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X3),u1_pre_topc(X3))
      | ~ l1_pre_topc(X3)
      | m1_pre_topc(X3,sK0) ) ),
    inference(forward_demodulation,[],[f310,f69])).

fof(f310,plain,(
    ! [X3] :
      ( m1_subset_1(sK4(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK3(sK0,X3),u1_pre_topc(X3))
      | ~ r1_tarski(k2_struct_0(X3),k2_struct_0(sK0))
      | ~ l1_pre_topc(X3)
      | m1_pre_topc(X3,sK0) ) ),
    inference(resolution,[],[f55,f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f560,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1))
    | ~ m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f559,f285])).

fof(f285,plain,
    ( r2_hidden(sK4(sK0,sK2),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1)) ),
    inference(forward_demodulation,[],[f284,f143])).

fof(f284,plain,
    ( r2_hidden(sK4(sK0,sK2),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f283,f105])).

fof(f283,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK2),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK2)) ),
    inference(forward_demodulation,[],[f282,f118])).

fof(f282,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK2),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f281,f96])).

fof(f281,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK2),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK2))
    | m1_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f277,f41])).

fof(f277,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
    | r2_hidden(sK4(sK0,sK2),u1_pre_topc(sK0))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2)
    | m1_pre_topc(sK2,sK0) ),
    inference(superposition,[],[f269,f71])).

fof(f269,plain,(
    ! [X3] :
      ( ~ r1_tarski(k2_struct_0(X3),u1_struct_0(sK0))
      | r2_hidden(sK4(sK0,X3),u1_pre_topc(sK0))
      | r2_hidden(sK3(sK0,X3),u1_pre_topc(X3))
      | ~ l1_pre_topc(X3)
      | m1_pre_topc(X3,sK0) ) ),
    inference(forward_demodulation,[],[f261,f69])).

fof(f261,plain,(
    ! [X3] :
      ( r2_hidden(sK4(sK0,X3),u1_pre_topc(sK0))
      | r2_hidden(sK3(sK0,X3),u1_pre_topc(X3))
      | ~ r1_tarski(k2_struct_0(X3),k2_struct_0(sK0))
      | ~ l1_pre_topc(X3)
      | m1_pre_topc(X3,sK0) ) ),
    inference(resolution,[],[f56,f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
      | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f559,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1))
    | ~ r2_hidden(sK4(sK0,sK2),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK4(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f463,f557])).

fof(f557,plain,(
    sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f556,f105])).

fof(f556,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f555,f69])).

fof(f555,plain,
    ( sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f554,f37])).

fof(f554,plain,
    ( sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f553,f96])).

fof(f553,plain,
    ( sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f552,f209])).

fof(f552,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f551,f105])).

fof(f551,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f550,f69])).

fof(f550,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f549,f37])).

fof(f549,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f548,f96])).

fof(f548,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f547])).

fof(f547,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f546,f439])).

fof(f439,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | sK3(X0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(X0,sK2),u1_struct_0(sK1))
      | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(X0))
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f438,f118])).

fof(f438,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(X0))
      | sK3(X0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(X0,sK2),u1_struct_0(sK1))
      | r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f437,f71])).

fof(f437,plain,(
    ! [X0] :
      ( sK3(X0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(X0,sK2),u1_struct_0(sK1))
      | r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | m1_pre_topc(sK2,X0)
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f436,f118])).

fof(f436,plain,(
    ! [X0] :
      ( sK3(X0,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(X0,sK2),u1_struct_0(sK2))
      | r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | m1_pre_topc(sK2,X0)
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f435,f71])).

fof(f435,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | sK3(X0,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(X0,sK2),k2_struct_0(sK2))
      | m1_pre_topc(sK2,X0)
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f430,f41])).

fof(f430,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | sK3(X0,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(X0,sK2),k2_struct_0(sK2))
      | m1_pre_topc(sK2,X0)
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X0))
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f57,f143])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK4(X0,X1),k2_struct_0(X1))
      | m1_pre_topc(X1,X0)
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f546,plain,
    ( ~ r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1))
    | ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f545,f258])).

fof(f258,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X0,u1_pre_topc(sK1)) ) ),
    inference(subsumption_resolution,[],[f257,f37])).

fof(f257,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(sK5(sK0,sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f256,f95])).

fof(f256,plain,(
    ! [X0,X5,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f50,f59])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f545,plain,
    ( sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1)) ),
    inference(resolution,[],[f544,f255])).

fof(f255,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK0,sK1,X0),u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X0,u1_pre_topc(sK1)) ) ),
    inference(subsumption_resolution,[],[f254,f37])).

fof(f254,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | r2_hidden(sK5(sK0,sK1,X0),u1_pre_topc(sK0))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f253,f95])).

fof(f253,plain,(
    ! [X0,X5,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f51,f59])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X0))
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f544,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK3(sK0,sK2)),u1_pre_topc(sK0))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(trivial_inequality_removal,[],[f543])).

fof(f543,plain,
    ( sK3(sK0,sK2) != sK3(sK0,sK2)
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_hidden(sK5(sK0,sK1,sK3(sK0,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f542])).

fof(f542,plain,
    ( sK3(sK0,sK2) != sK3(sK0,sK2)
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ r2_hidden(sK5(sK0,sK1,sK3(sK0,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1)) ),
    inference(superposition,[],[f541,f504])).

fof(f504,plain,
    ( sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(sK0,sK2)),u1_struct_0(sK1))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f503,f37])).

fof(f503,plain,
    ( sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(sK0,sK2)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f502,f96])).

fof(f502,plain,
    ( sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(sK0,sK2)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f497,f105])).

fof(f497,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
    | m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(sK0,sK2)),u1_struct_0(sK1)) ),
    inference(superposition,[],[f445,f69])).

fof(f445,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(X0))
      | sK3(X0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(X0,sK2),u1_struct_0(sK1))
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | sK3(X0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(X0,sK2)),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f444,f209])).

fof(f444,plain,(
    ! [X0] :
      ( sK3(X0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(X0,sK2),u1_struct_0(sK1))
      | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(X0))
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | sK3(X0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(X0,sK2)),u1_struct_0(sK1))
      | ~ m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f439,f363])).

fof(f363,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK1))
      | k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,X0),u1_struct_0(sK1)) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(forward_demodulation,[],[f362,f70])).

fof(f362,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,X0),k2_struct_0(sK1)) = X0 ) ),
    inference(subsumption_resolution,[],[f361,f37])).

fof(f361,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,X0),k2_struct_0(sK1)) = X0
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f360,f95])).

fof(f360,plain,(
    ! [X0,X5,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X5),k2_struct_0(X1)) = X5
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f52,f59])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X5),k2_struct_0(X1)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f541,plain,(
    ! [X3] :
      ( sK3(sK0,sK2) != k9_subset_1(u1_struct_0(sK1),X3,u1_struct_0(sK1))
      | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK4(sK0,sK2),u1_struct_0(sK1))
      | ~ r2_hidden(X3,u1_pre_topc(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f540,f118])).

fof(f540,plain,(
    ! [X3] :
      ( sK3(sK0,sK2) != k9_subset_1(u1_struct_0(sK1),X3,u1_struct_0(sK1))
      | ~ r2_hidden(X3,u1_pre_topc(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK0,sK2),u1_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f539,f118])).

fof(f539,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_pre_topc(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(sK0,sK2) != k9_subset_1(u1_struct_0(sK2),X3,u1_struct_0(sK2))
      | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK0,sK2),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f538,f105])).

fof(f538,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_pre_topc(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(sK0,sK2) != k9_subset_1(u1_struct_0(sK2),X3,u1_struct_0(sK2))
      | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK0,sK2),u1_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f537,f118])).

fof(f537,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_pre_topc(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(sK0,sK2) != k9_subset_1(u1_struct_0(sK2),X3,u1_struct_0(sK2))
      | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK0,sK2),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f536,f41])).

fof(f536,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_pre_topc(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK2)
      | sK3(sK0,sK2) != k9_subset_1(u1_struct_0(sK2),X3,u1_struct_0(sK2))
      | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK0,sK2),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f531,f96])).

fof(f531,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_pre_topc(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_pre_topc(sK2,sK0)
      | ~ l1_pre_topc(sK2)
      | sK3(sK0,sK2) != k9_subset_1(u1_struct_0(sK2),X3,u1_struct_0(sK2))
      | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK2),sK4(sK0,sK2),u1_struct_0(sK2)) ) ),
    inference(superposition,[],[f522,f71])).

fof(f522,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(k2_struct_0(X6),u1_struct_0(sK0))
      | ~ r2_hidden(X5,u1_pre_topc(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_pre_topc(X6,sK0)
      | ~ l1_pre_topc(X6)
      | k9_subset_1(u1_struct_0(X6),X5,k2_struct_0(X6)) != sK3(sK0,X6)
      | sK3(sK0,X6) = k9_subset_1(u1_struct_0(X6),sK4(sK0,X6),k2_struct_0(X6)) ) ),
    inference(forward_demodulation,[],[f512,f69])).

fof(f512,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,u1_pre_topc(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_pre_topc(X6,sK0)
      | ~ r1_tarski(k2_struct_0(X6),k2_struct_0(sK0))
      | ~ l1_pre_topc(X6)
      | k9_subset_1(u1_struct_0(X6),X5,k2_struct_0(X6)) != sK3(sK0,X6)
      | sK3(sK0,X6) = k9_subset_1(u1_struct_0(X6),sK4(sK0,X6),k2_struct_0(X6)) ) ),
    inference(resolution,[],[f469,f37])).

fof(f469,plain,(
    ! [X4,X2,X3] :
      ( ~ l1_pre_topc(X4)
      | ~ r2_hidden(X3,u1_pre_topc(X4))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | m1_pre_topc(X2,X4)
      | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X4))
      | ~ l1_pre_topc(X2)
      | k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2)) != sK3(X4,X2)
      | sK3(X4,X2) = k9_subset_1(u1_struct_0(X2),sK4(X4,X2),k2_struct_0(X2)) ) ),
    inference(duplicate_literal_removal,[],[f466])).

fof(f466,plain,(
    ! [X4,X2,X3] :
      ( k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2)) != sK3(X4,X2)
      | ~ r2_hidden(X3,u1_pre_topc(X4))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | m1_pre_topc(X2,X4)
      | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X4))
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X4)
      | sK3(X4,X2) = k9_subset_1(u1_struct_0(X2),sK4(X4,X2),k2_struct_0(X2))
      | m1_pre_topc(X2,X4)
      | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X4))
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f58,f57])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(X1,X0)
      | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f463,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK1),X0,u1_struct_0(sK1)),u1_pre_topc(sK1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f462,f70])).

fof(f462,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK1),X0,k2_struct_0(sK1)),u1_pre_topc(sK1)) ) ),
    inference(forward_demodulation,[],[f461,f70])).

fof(f461,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0,k2_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK1),X0,k2_struct_0(sK1)),u1_pre_topc(sK1)) ) ),
    inference(subsumption_resolution,[],[f460,f37])).

fof(f460,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK1),X0,k2_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK1),X0,k2_struct_0(sK1)),u1_pre_topc(sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f459,f95])).

fof(f459,plain,(
    ! [X6,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),u1_pre_topc(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f66,f59])).

fof(f66,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),u1_pre_topc(X1))
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f616,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1)) ),
    inference(duplicate_literal_removal,[],[f615])).

fof(f615,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1)) ),
    inference(resolution,[],[f614,f258])).

fof(f614,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f613,f566])).

fof(f613,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1)) ),
    inference(resolution,[],[f612,f255])).

fof(f612,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK3(sK0,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f611,f105])).

fof(f611,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,sK1,sK3(sK0,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f610,f69])).

fof(f610,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,sK1,sK3(sK0,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f609,f37])).

fof(f609,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,sK1,sK3(sK0,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f608,f96])).

fof(f608,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ r2_hidden(sK5(sK0,sK1,sK3(sK0,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f607,f566])).

fof(f607,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ r2_hidden(sK3(sK0,sK2),u1_pre_topc(sK1))
    | ~ r2_hidden(sK5(sK0,sK1,sK3(sK0,sK2)),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(equality_resolution,[],[f573])).

fof(f573,plain,(
    ! [X0] :
      ( sK3(X0,sK2) != sK3(sK0,sK2)
      | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(X0))
      | ~ r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | ~ r2_hidden(sK5(sK0,sK1,sK3(sK0,sK2)),u1_pre_topc(X0))
      | ~ m1_subset_1(sK5(sK0,sK1,sK3(sK0,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f491,f572])).

fof(f572,plain,(
    sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(sK0,sK2)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f571,f105])).

fof(f571,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(sK0,sK2)),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f570,f69])).

fof(f570,plain,
    ( sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f569,f37])).

fof(f569,plain,
    ( sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f568,f96])).

fof(f568,plain,
    ( sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(sK0,sK2)),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(sK0))
    | m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f567,f209])).

fof(f567,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | sK3(sK0,sK2) = k9_subset_1(u1_struct_0(sK1),sK5(sK0,sK1,sK3(sK0,sK2)),u1_struct_0(sK1)) ),
    inference(resolution,[],[f566,f363])).

fof(f491,plain,(
    ! [X0,X1] :
      ( sK3(X0,sK2) != k9_subset_1(u1_struct_0(sK1),X1,u1_struct_0(sK1))
      | ~ r1_tarski(u1_struct_0(sK1),k2_struct_0(X0))
      | ~ r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f490,f118])).

fof(f490,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(u1_struct_0(sK2),k2_struct_0(X0))
      | sK3(X0,sK2) != k9_subset_1(u1_struct_0(sK1),X1,u1_struct_0(sK1))
      | ~ r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f489,f71])).

fof(f489,plain,(
    ! [X0,X1] :
      ( sK3(X0,sK2) != k9_subset_1(u1_struct_0(sK1),X1,u1_struct_0(sK1))
      | ~ r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2,X0)
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f488,f118])).

fof(f488,plain,(
    ! [X0,X1] :
      ( sK3(X0,sK2) != k9_subset_1(u1_struct_0(sK2),X1,u1_struct_0(sK2))
      | ~ r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2,X0)
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f487,f71])).

fof(f487,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | sK3(X0,sK2) != k9_subset_1(u1_struct_0(sK2),X1,k2_struct_0(sK2))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2,X0)
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f467,f41])).

fof(f467,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,sK2),u1_pre_topc(sK1))
      | sK3(X0,sK2) != k9_subset_1(u1_struct_0(sK2),X1,k2_struct_0(sK2))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2,X0)
      | ~ r1_tarski(k2_struct_0(sK2),k2_struct_0(X0))
      | ~ l1_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f58,f143])).

%------------------------------------------------------------------------------
