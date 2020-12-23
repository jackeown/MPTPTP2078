%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t59_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:45 EDT 2019

% Result     : Theorem 148.99s
% Output     : Refutation 148.99s
% Verified   : 
% Statistics : Number of formulae       :  161 (3658 expanded)
%              Number of leaves         :   20 (1171 expanded)
%              Depth                    :   30
%              Number of atoms          :  545 (12670 expanded)
%              Number of equality atoms :   81 (1058 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19600,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19599,f15294])).

fof(f15294,plain,(
    r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f15293,f2323])).

fof(f2323,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f1212,f638])).

fof(f638,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(subsumption_resolution,[],[f637,f252])).

fof(f252,plain,(
    l1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f179,f95])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',dt_l1_pre_topc)).

fof(f179,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f141,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',dt_g1_pre_topc)).

fof(f141,plain,(
    m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f88,f96])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',dt_u1_pre_topc)).

fof(f88,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f69,f68])).

fof(f68,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m1_pre_topc(X1,X0)
            & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ m1_pre_topc(X1,sK2)
          & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ m1_pre_topc(X1,X0)
          & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
     => ( ~ m1_pre_topc(sK3,X0)
        & m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m1_pre_topc(X1,X0)
          & m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
           => m1_pre_topc(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',t59_pre_topc)).

fof(f637,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(superposition,[],[f624,f93])).

fof(f93,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',d3_struct_0)).

fof(f624,plain,(
    r1_tarski(u1_struct_0(sK3),k2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(forward_demodulation,[],[f412,f204])).

fof(f204,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f193,f93])).

fof(f193,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f192,f95])).

fof(f192,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f188,f141])).

fof(f188,plain,
    ( l1_pre_topc(sK3)
    | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(resolution,[],[f150,f120])).

fof(f150,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f89,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',dt_m1_pre_topc)).

fof(f89,plain,(
    m1_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(cnf_transformation,[],[f70])).

fof(f412,plain,(
    r1_tarski(k2_struct_0(sK3),k2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(resolution,[],[f411,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
          & ( ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = sK4(X0,X1)
              & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
              & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
                    & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
                    & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f74,f77,f76,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X1))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r2_hidden(X2,u1_pre_topc(X0)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                & r2_hidden(X4,u1_pre_topc(X1))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | r2_hidden(X2,u1_pre_topc(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = sK4(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X1))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
          & r2_hidden(X4,u1_pre_topc(X1))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = X2
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
          & r2_hidden(X7,u1_pre_topc(X1))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != X2
                  | ~ r2_hidden(X3,u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r2_hidden(X2,u1_pre_topc(X0)) )
            & ( ? [X4] :
                  ( k9_subset_1(u1_struct_0(X0),X4,k2_struct_0(X0)) = X2
                  & r2_hidden(X4,u1_pre_topc(X1))
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
              | r2_hidden(X2,u1_pre_topc(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X5] :
              ( ( ( r2_hidden(X5,u1_pre_topc(X0))
                  | ! [X6] :
                      ( k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
                      | ~ r2_hidden(X6,u1_pre_topc(X1))
                      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ? [X7] :
                      ( k9_subset_1(u1_struct_0(X0),X7,k2_struct_0(X0)) = X5
                      & r2_hidden(X7,u1_pre_topc(X1))
                      & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ r2_hidden(X5,u1_pre_topc(X0)) ) )
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f73])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
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
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
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
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2] :
            ( ( r2_hidden(X2,u1_pre_topc(X1))
            <=> ? [X3] :
                  ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                  & r2_hidden(X3,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f411,plain,(
    sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f202,f179])).

fof(f202,plain,
    ( sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f200,f192])).

fof(f200,plain,
    ( sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f151,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f47,f66,f65])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',d9_pre_topc)).

fof(f151,plain,
    ( ~ sP1(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),sK3)
    | sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f89,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f66])).

fof(f1212,plain,(
    u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f1211,f179])).

fof(f1211,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f1210,f178])).

fof(f178,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(resolution,[],[f141,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1210,plain,
    ( u1_struct_0(sK2) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(equality_resolution,[],[f405])).

fof(f405,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0
      | u1_struct_0(sK2) = u1_struct_0(X0)
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f176,f97])).

fof(f97,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',abstractness_v1_pre_topc)).

fof(f176,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | u1_struct_0(sK2) = X0 ) ),
    inference(resolution,[],[f141,f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',free_g1_pre_topc)).

fof(f15293,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2)) ),
    inference(forward_demodulation,[],[f15292,f204])).

fof(f15292,plain,
    ( ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2)) ),
    inference(forward_demodulation,[],[f15291,f148])).

fof(f148,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f140,f93])).

fof(f140,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f88,f95])).

fof(f15291,plain,
    ( r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f15263,f233])).

fof(f233,plain,(
    ~ sP0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f173,f192])).

fof(f173,plain,
    ( ~ sP0(sK3,sK2)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f149,f143])).

fof(f143,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f88,f110])).

fof(f149,plain,
    ( ~ sP1(sK2,sK3)
    | ~ sP0(sK3,sK2) ),
    inference(resolution,[],[f90,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f90,plain,(
    ~ m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f15263,plain,
    ( sP0(sK3,sK2)
    | r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(resolution,[],[f15203,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r2_hidden(sK5(X0,X1),u1_pre_topc(X1))
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f15203,plain,(
    ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f15202,f2323])).

fof(f15202,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(forward_demodulation,[],[f15201,f204])).

fof(f15201,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f15200,f411])).

fof(f15200,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f15199,f90])).

fof(f15199,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | m1_pre_topc(sK3,sK2)
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f15198,f192])).

fof(f15198,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK3)
    | m1_pre_topc(sK3,sK2)
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f15171,f233])).

fof(f15171,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | sP0(sK3,sK2)
    | ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK3)
    | m1_pre_topc(sK3,sK2)
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(trivial_inequality_removal,[],[f15170])).

fof(f15170,plain,
    ( sK4(sK3,sK2) != sK4(sK3,sK2)
    | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | sP0(sK3,sK2)
    | ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK3)
    | m1_pre_topc(sK3,sK2)
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(duplicate_literal_removal,[],[f15153])).

fof(f15153,plain,
    ( sK4(sK3,sK2) != sK4(sK3,sK2)
    | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | sP0(sK3,sK2)
    | ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ l1_pre_topc(sK3)
    | ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | m1_pre_topc(sK3,sK2)
    | ~ r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ sP0(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(superposition,[],[f2519,f1225])).

fof(f1225,plain,(
    ! [X4,X5] :
      ( k9_subset_1(u1_struct_0(X4),sK6(X4,X5,sK4(X4,sK2)),k2_struct_0(X4)) = sK4(X4,sK2)
      | ~ l1_pre_topc(X4)
      | ~ r1_tarski(k2_struct_0(X4),u1_struct_0(sK2))
      | m1_pre_topc(X4,sK2)
      | ~ r2_hidden(sK4(X4,sK2),u1_pre_topc(X4))
      | ~ sP0(X4,X5) ) ),
    inference(resolution,[],[f304,f103])).

fof(f103,plain,(
    ! [X0,X5,X1] :
      ( k9_subset_1(u1_struct_0(X0),sK6(X0,X1,X5),k2_struct_0(X0)) = X5
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f304,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(k2_struct_0(X0),u1_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f298,f148])).

fof(f298,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(sK2)) ) ),
    inference(resolution,[],[f159,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f159,plain,(
    ! [X1] :
      ( ~ sP0(X1,sK2)
      | m1_pre_topc(X1,sK2)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f143,f99])).

fof(f2519,plain,(
    ! [X12,X13] :
      ( k9_subset_1(u1_struct_0(X13),sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X12),k2_struct_0(X13)) != sK4(X13,sK2)
      | ~ r2_hidden(X12,u1_pre_topc(sK3))
      | sP0(X13,sK2)
      | ~ r1_tarski(k2_struct_0(X13),u1_struct_0(sK2))
      | ~ r2_hidden(sK4(X13,sK2),u1_pre_topc(X13)) ) ),
    inference(forward_demodulation,[],[f2518,f148])).

fof(f2518,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,u1_pre_topc(sK3))
      | sP0(X13,sK2)
      | k9_subset_1(u1_struct_0(X13),sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X12),k2_struct_0(X13)) != sK4(X13,sK2)
      | ~ r2_hidden(sK4(X13,sK2),u1_pre_topc(X13))
      | ~ r1_tarski(k2_struct_0(X13),k2_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f2503,f2355])).

fof(f2355,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X0,u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f2326,f473])).

fof(f473,plain,(
    ! [X7] :
      ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X7,u1_pre_topc(sK3)) ) ),
    inference(resolution,[],[f194,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',t4_subset)).

fof(f194,plain,(
    m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(resolution,[],[f192,f96])).

fof(f2326,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X0,u1_pre_topc(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(backward_demodulation,[],[f1212,f413])).

fof(f413,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
      | ~ r2_hidden(X0,u1_pre_topc(sK3))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f411,f101])).

fof(f101,plain,(
    ! [X0,X5,X1] :
      ( m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2503,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X12,u1_pre_topc(sK3))
      | sP0(X13,sK2)
      | k9_subset_1(u1_struct_0(X13),sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X12),k2_struct_0(X13)) != sK4(X13,sK2)
      | ~ m1_subset_1(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X12),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(sK4(X13,sK2),u1_pre_topc(X13))
      | ~ r1_tarski(k2_struct_0(X13),k2_struct_0(sK2)) ) ),
    inference(resolution,[],[f2475,f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),X3,k2_struct_0(X0)) != sK4(X0,X1)
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2475,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1),u1_pre_topc(sK2))
      | ~ r2_hidden(X1,u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f2456,f473])).

fof(f2456,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1),u1_pre_topc(sK2))
      | ~ r2_hidden(X1,u1_pre_topc(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(backward_demodulation,[],[f1218,f414])).

fof(f414,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK3,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X1),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
      | ~ r2_hidden(X1,u1_pre_topc(sK3))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f411,f102])).

fof(f102,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X1))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f1218,plain,(
    u1_pre_topc(sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f1217,f179])).

fof(f1217,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(subsumption_resolution,[],[f1216,f178])).

fof(f1216,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(equality_resolution,[],[f408])).

fof(f408,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0
      | u1_pre_topc(sK2) = u1_pre_topc(X0)
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f177,f97])).

fof(f177,plain,(
    ! [X2,X3] :
      ( g1_pre_topc(X3,X2) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      | u1_pre_topc(sK2) = X2 ) ),
    inference(resolution,[],[f141,f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f19599,plain,(
    ~ r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2)) ),
    inference(subsumption_resolution,[],[f19589,f15203])).

fof(f19589,plain,
    ( r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r2_hidden(sK5(sK3,sK2),u1_pre_topc(sK2)) ),
    inference(superposition,[],[f19506,f19508])).

fof(f19508,plain,(
    k3_xboole_0(sK5(sK3,sK2),u1_struct_0(sK3)) = sK4(sK3,sK2) ),
    inference(subsumption_resolution,[],[f19507,f15203])).

fof(f19507,plain,
    ( k3_xboole_0(sK5(sK3,sK2),u1_struct_0(sK3)) = sK4(sK3,sK2)
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(subsumption_resolution,[],[f19466,f2323])).

fof(f19466,plain,
    ( k3_xboole_0(sK5(sK3,sK2),u1_struct_0(sK3)) = sK4(sK3,sK2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(backward_demodulation,[],[f706,f1537])).

fof(f1537,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK5(sK3,sK2),u1_struct_0(sK3)) = sK4(sK3,sK2)
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(forward_demodulation,[],[f1536,f204])).

fof(f1536,plain,
    ( ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK3),sK5(sK3,sK2),k2_struct_0(sK3)) = sK4(sK3,sK2)
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(forward_demodulation,[],[f243,f204])).

fof(f243,plain,
    ( ~ r1_tarski(k2_struct_0(sK3),u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK3),sK5(sK3,sK2),k2_struct_0(sK3)) = sK4(sK3,sK2)
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3)) ),
    inference(forward_demodulation,[],[f237,f148])).

fof(f237,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK5(sK3,sK2),k2_struct_0(sK3)) = sK4(sK3,sK2)
    | r2_hidden(sK4(sK3,sK2),u1_pre_topc(sK3))
    | ~ r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) ),
    inference(resolution,[],[f233,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X0),sK5(X0,X1),k2_struct_0(X0)) = sK4(X0,X1)
      | r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
      | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f706,plain,(
    ! [X6] : k3_xboole_0(X6,u1_struct_0(sK3)) = k9_subset_1(u1_struct_0(sK3),X6,u1_struct_0(sK3)) ),
    inference(resolution,[],[f549,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',redefinition_k9_subset_1)).

fof(f549,plain,(
    m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f203,f204])).

fof(f203,plain,(
    m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f193,f94])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',dt_k2_struct_0)).

fof(f19506,plain,(
    ! [X3] :
      ( r2_hidden(k3_xboole_0(X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(subsumption_resolution,[],[f19505,f18712])).

fof(f18712,plain,(
    ! [X5] : m1_subset_1(k3_xboole_0(X5,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(subsumption_resolution,[],[f18707,f549])).

fof(f18707,plain,(
    ! [X5] :
      ( m1_subset_1(k3_xboole_0(X5,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(superposition,[],[f705,f129])).

fof(f705,plain,(
    ! [X5] : m1_subset_1(k9_subset_1(u1_struct_0(sK3),X5,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f549,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/pre_topc__t59_pre_topc.p',dt_k9_subset_1)).

fof(f19505,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k3_xboole_0(X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_hidden(k3_xboole_0(X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(forward_demodulation,[],[f19464,f706])).

fof(f19464,plain,(
    ! [X3] :
      ( r2_hidden(k3_xboole_0(X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X3,u1_pre_topc(sK2)) ) ),
    inference(backward_demodulation,[],[f706,f2474])).

fof(f2474,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ r2_hidden(X3,u1_pre_topc(sK2))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3)) ) ),
    inference(subsumption_resolution,[],[f2454,f184])).

fof(f184,plain,(
    ! [X7] :
      ( m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ r2_hidden(X7,u1_pre_topc(sK2)) ) ),
    inference(resolution,[],[f141,f131])).

fof(f2454,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_pre_topc(sK2))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3)) ) ),
    inference(backward_demodulation,[],[f1218,f2325])).

fof(f2325,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ) ),
    inference(backward_demodulation,[],[f1212,f2033])).

fof(f2033,plain,(
    ! [X3] :
      ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ) ),
    inference(forward_demodulation,[],[f2032,f204])).

fof(f2032,plain,(
    ! [X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,u1_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(forward_demodulation,[],[f416,f204])).

fof(f416,plain,(
    ! [X3] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)),u1_pre_topc(sK3))
      | ~ r2_hidden(X3,u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X3,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    inference(resolution,[],[f411,f135])).

fof(f135,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),u1_pre_topc(X0))
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,u1_pre_topc(X0))
      | k9_subset_1(u1_struct_0(X0),X6,k2_struct_0(X0)) != X5
      | ~ r2_hidden(X6,u1_pre_topc(X1))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).
%------------------------------------------------------------------------------
