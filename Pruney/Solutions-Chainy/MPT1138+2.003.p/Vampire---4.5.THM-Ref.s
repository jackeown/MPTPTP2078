%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 (1408 expanded)
%              Number of leaves         :   14 ( 546 expanded)
%              Depth                    :   29
%              Number of atoms          :  445 (9984 expanded)
%              Number of equality atoms :   11 (  66 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f666,plain,(
    $false ),
    inference(resolution,[],[f665,f42])).

fof(f42,plain,(
    ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    & r1_orders_2(sK0,sK2,sK3)
    & r1_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(sK0,X1,X3)
                  & r1_orders_2(sK0,X2,X3)
                  & r1_orders_2(sK0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(sK0,X1,X3)
                & r1_orders_2(sK0,X2,X3)
                & r1_orders_2(sK0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(sK0,sK1,X3)
              & r1_orders_2(sK0,X2,X3)
              & r1_orders_2(sK0,sK1,X2)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_orders_2(sK0,sK1,X3)
            & r1_orders_2(sK0,X2,X3)
            & r1_orders_2(sK0,sK1,X2)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r1_orders_2(sK0,sK1,X3)
          & r1_orders_2(sK0,sK2,X3)
          & r1_orders_2(sK0,sK1,sK2)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ~ r1_orders_2(sK0,sK1,X3)
        & r1_orders_2(sK0,sK2,X3)
        & r1_orders_2(sK0,sK1,sK2)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_orders_2(sK0,sK1,sK3)
      & r1_orders_2(sK0,sK2,sK3)
      & r1_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X1,X3)
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X1,X3)
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f665,plain,(
    r1_orders_2(sK0,sK1,sK3) ),
    inference(resolution,[],[f652,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f652,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK3) ),
    inference(resolution,[],[f647,f39])).

fof(f39,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f647,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK3) ),
    inference(resolution,[],[f645,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1) ) ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f645,plain,(
    r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0)) ),
    inference(resolution,[],[f643,f379])).

fof(f379,plain,(
    r2_hidden(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f375,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f375,plain,(
    r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(resolution,[],[f372,f193])).

fof(f193,plain,(
    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ),
    inference(resolution,[],[f175,f159])).

fof(f159,plain,(
    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f151,f37])).

fof(f151,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f149,f38])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f149,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f139,f40])).

fof(f40,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f139,plain,(
    ! [X37,X38] :
      ( ~ r1_orders_2(sK0,X38,X37)
      | ~ m1_subset_1(X37,u1_struct_0(sK0))
      | ~ m1_subset_1(X38,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f123,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1) ) ),
    inference(resolution,[],[f53,f36])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f123,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f120,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(k4_tarski(sK1,sK2),X0),k2_zfmisc_1(u1_orders_2(sK0),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f119,f37])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(k4_tarski(sK1,sK2),X0),k2_zfmisc_1(u1_orders_2(sK0),X1)) ) ),
    inference(resolution,[],[f117,f38])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(k4_tarski(sK1,sK2),X0),k2_zfmisc_1(u1_orders_2(sK0),X1)) ) ),
    inference(resolution,[],[f97,f40])).

fof(f97,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ r1_orders_2(sK0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X3,X4)
      | r2_hidden(k4_tarski(k4_tarski(X2,X1),X3),k2_zfmisc_1(u1_orders_2(sK0),X4)) ) ),
    inference(resolution,[],[f95,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f175,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f173,f59])).

fof(f173,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(k4_tarski(sK2,sK3),X0),k2_zfmisc_1(u1_orders_2(sK0),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f171,f38])).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(k4_tarski(sK2,sK3),X0),k2_zfmisc_1(u1_orders_2(sK0),X1)) ) ),
    inference(resolution,[],[f118,f39])).

fof(f118,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X3)
      | r2_hidden(k4_tarski(k4_tarski(sK2,sK3),X2),k2_zfmisc_1(u1_orders_2(sK0),X3)) ) ),
    inference(resolution,[],[f97,f41])).

fof(f41,plain,(
    r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f372,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f371])).

fof(f371,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ),
    inference(resolution,[],[f252,f235])).

fof(f235,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0,u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_orders_2(sK0)) ) ),
    inference(condensation,[],[f229])).

fof(f229,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X5,u1_orders_2(sK0))
      | r2_hidden(sK8(X5,u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f214,f59])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,u1_struct_0(sK0),u1_struct_0(sK0)),X1),k2_zfmisc_1(u1_struct_0(sK0),X2))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f88,f36])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,u1_orders_2(X1))
      | ~ r2_hidden(X2,X3)
      | r2_hidden(k4_tarski(sK8(X0,u1_struct_0(X1),u1_struct_0(X1)),X2),k2_zfmisc_1(u1_struct_0(X1),X3)) ) ),
    inference(resolution,[],[f86,f61])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,u1_struct_0(X1),u1_struct_0(X1)),u1_struct_0(X1))
      | ~ r2_hidden(X0,u1_orders_2(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,X3)
      | r2_hidden(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(sK8(X0,X1,X2),X2)
        & r2_hidden(sK7(X0,X1,X2),X1)
        & k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f19,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
     => ( r2_hidden(sK8(X0,X1,X2),X2)
        & r2_hidden(sK7(X0,X1,X2),X1)
        & k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0 ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( r2_hidden(X5,X2)
          & r2_hidden(X4,X1)
          & k4_tarski(X4,X5) = X0 )
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ~ ( ! [X4,X5] :
              ~ ( r2_hidden(X5,X2)
                & r2_hidden(X4,X1)
                & k4_tarski(X4,X5) = X0 )
          & r2_hidden(X0,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

fof(f252,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(k4_tarski(sK2,sK3),u1_struct_0(sK0),u1_struct_0(sK0)),X0)
      | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK0),X0))
      | ~ r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ) ),
    inference(superposition,[],[f172,f204])).

fof(f204,plain,(
    k4_tarski(sK2,sK3) = k4_tarski(sK7(k4_tarski(sK2,sK3),u1_struct_0(sK0),u1_struct_0(sK0)),sK8(k4_tarski(sK2,sK3),u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(resolution,[],[f193,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_orders_2(sK0))
      | k4_tarski(sK7(X0,u1_struct_0(sK0),u1_struct_0(sK0)),sK8(X0,u1_struct_0(sK0),u1_struct_0(sK0))) = X0 ) ),
    inference(resolution,[],[f103,f36])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | k4_tarski(sK7(X0,u1_struct_0(X1),u1_struct_0(X1)),sK8(X0,u1_struct_0(X1),u1_struct_0(X1))) = X0
      | ~ r2_hidden(X0,u1_orders_2(X1)) ) ),
    inference(resolution,[],[f56,f50])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,X3)
      | k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,u1_struct_0(sK0),u1_struct_0(sK0)),X1),k2_zfmisc_1(u1_struct_0(sK0),X2))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f87,f36])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,u1_orders_2(X1))
      | ~ r2_hidden(X2,X3)
      | r2_hidden(k4_tarski(sK7(X0,u1_struct_0(X1),u1_struct_0(X1)),X2),k2_zfmisc_1(u1_struct_0(X1),X3)) ) ),
    inference(resolution,[],[f85,f61])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,u1_struct_0(X1),u1_struct_0(X1)),u1_struct_0(X1))
      | ~ r2_hidden(X0,u1_orders_2(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f57,f50])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X0,X3)
      | r2_hidden(sK7(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f643,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0)) ),
    inference(resolution,[],[f641,f193])).

fof(f641,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK2,X0),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f626,f270])).

fof(f270,plain,(
    r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f264,f59])).

fof(f264,plain,(
    r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(resolution,[],[f262,f159])).

fof(f262,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f261])).

fof(f261,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(resolution,[],[f247,f235])).

fof(f247,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(k4_tarski(sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),X0)
      | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),X0))
      | ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ) ),
    inference(superposition,[],[f172,f161])).

fof(f161,plain,(
    k4_tarski(sK1,sK2) = k4_tarski(sK7(k4_tarski(sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),sK8(k4_tarski(sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(resolution,[],[f159,f121])).

fof(f626,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0))
      | ~ r2_hidden(k4_tarski(sK2,X0),u1_orders_2(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f618,f269])).

fof(f269,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f264,f60])).

fof(f618,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK2,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(sK2,X3),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(sK1,X3),u1_orders_2(sK0))
      | ~ r2_hidden(sK1,u1_struct_0(sK0))
      | ~ r2_hidden(X3,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f616,f159])).

fof(f616,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X0,X2),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f516,f36])).

fof(f516,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(sK0)
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X2,X0),u1_orders_2(sK0))
      | ~ r2_hidden(k4_tarski(X2,X1),u1_orders_2(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f257,f35])).

fof(f35,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f257,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ r2_hidden(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X0,X2),u1_orders_2(sK0))
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f108,f51])).

fof(f51,plain,(
    ! [X0] :
      ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r8_relat_2(u1_orders_2(sK0),X3)
      | ~ r2_hidden(k4_tarski(X2,X0),u1_orders_2(sK0))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X3)
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X2,X1),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f43,f65])).

fof(f65,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f64,f36])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_relat_1(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f50,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f43,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ r8_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X5,X7),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
              & r2_hidden(sK6(X0,X1),X1)
              & r2_hidden(sK5(X0,X1),X1)
              & r2_hidden(sK4(X0,X1),X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2,X3,X4] :
          ( ~ r2_hidden(k4_tarski(X2,X4),X0)
          & r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3,X4] :
                ( r2_hidden(k4_tarski(X2,X4),X0)
                | ~ r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k4_tarski(X2,X4),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:18:30 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.46  % (32339)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.47  % (32335)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.48  % (32341)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (32343)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.49  % (32352)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.49  % (32345)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (32337)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (32334)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (32337)Refutation not found, incomplete strategy% (32337)------------------------------
% 0.21/0.50  % (32337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (32337)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (32337)Memory used [KB]: 10618
% 0.21/0.50  % (32337)Time elapsed: 0.093 s
% 0.21/0.50  % (32337)------------------------------
% 0.21/0.50  % (32337)------------------------------
% 0.21/0.50  % (32346)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (32349)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (32354)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (32348)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (32351)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (32340)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (32356)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (32340)Refutation not found, incomplete strategy% (32340)------------------------------
% 0.21/0.52  % (32340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32340)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32340)Memory used [KB]: 10746
% 0.21/0.52  % (32340)Time elapsed: 0.075 s
% 0.21/0.52  % (32340)------------------------------
% 0.21/0.52  % (32340)------------------------------
% 0.21/0.52  % (32357)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (32336)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.53  % (32343)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f666,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(resolution,[],[f665,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ~r1_orders_2(sK0,sK1,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    (((~r1_orders_2(sK0,sK1,sK3) & r1_orders_2(sK0,sK2,sK3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v4_orders_2(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f23,f22,f21,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(sK0,X1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v4_orders_2(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(sK0,X1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,sK2,X3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,sK2,X3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r1_orders_2(sK0,sK1,sK3) & r1_orders_2(sK0,sK2,sK3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_orders_2(X0,X1,X3) & (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).
% 0.21/0.53  fof(f665,plain,(
% 0.21/0.53    r1_orders_2(sK0,sK1,sK3)),
% 0.21/0.53    inference(resolution,[],[f652,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f652,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK3)),
% 0.21/0.53    inference(resolution,[],[f647,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f647,plain,(
% 0.21/0.53    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK3)),
% 0.21/0.53    inference(resolution,[],[f645,f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f54,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    l1_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.53  fof(f645,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0))),
% 0.21/0.53    inference(resolution,[],[f643,f379])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    r2_hidden(sK3,u1_struct_0(sK0))),
% 0.21/0.53    inference(resolution,[],[f375,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.53    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f372,f193])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))),
% 0.21/0.53    inference(resolution,[],[f175,f159])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))),
% 0.21/0.53    inference(resolution,[],[f151,f37])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))),
% 0.21/0.53    inference(resolution,[],[f149,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))),
% 0.21/0.53    inference(resolution,[],[f139,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    r1_orders_2(sK0,sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ( ! [X37,X38] : (~r1_orders_2(sK0,X38,X37) | ~m1_subset_1(X37,u1_struct_0(sK0)) | ~m1_subset_1(X38,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f123,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f53,f36])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r2_hidden(X2,X3) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f120,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(k4_tarski(sK1,sK2),X0),k2_zfmisc_1(u1_orders_2(sK0),X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f119,f37])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(k4_tarski(sK1,sK2),X0),k2_zfmisc_1(u1_orders_2(sK0),X1))) )),
% 0.21/0.53    inference(resolution,[],[f117,f38])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(k4_tarski(sK1,sK2),X0),k2_zfmisc_1(u1_orders_2(sK0),X1))) )),
% 0.21/0.53    inference(resolution,[],[f97,f40])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X4,X2,X3,X1] : (~r1_orders_2(sK0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X3,X4) | r2_hidden(k4_tarski(k4_tarski(X2,X1),X3),k2_zfmisc_1(u1_orders_2(sK0),X4))) )),
% 0.21/0.53    inference(resolution,[],[f95,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r2_hidden(X2,X3) | r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f173,f59])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(k4_tarski(sK2,sK3),X0),k2_zfmisc_1(u1_orders_2(sK0),X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f171,f38])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(k4_tarski(sK2,sK3),X0),k2_zfmisc_1(u1_orders_2(sK0),X1))) )),
% 0.21/0.53    inference(resolution,[],[f118,f39])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r2_hidden(X2,X3) | r2_hidden(k4_tarski(k4_tarski(sK2,sK3),X2),k2_zfmisc_1(u1_orders_2(sK0),X3))) )),
% 0.21/0.53    inference(resolution,[],[f97,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    r1_orders_2(sK0,sK2,sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f372,plain,(
% 0.21/0.53    ~r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f371])).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) | ~r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) | ~r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))),
% 0.21/0.53    inference(resolution,[],[f252,f235])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK8(X0,u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) | ~r2_hidden(X0,u1_orders_2(sK0))) )),
% 0.21/0.53    inference(condensation,[],[f229])).
% 0.21/0.53  fof(f229,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (~r2_hidden(X3,X4) | ~r2_hidden(X5,u1_orders_2(sK0)) | r2_hidden(sK8(X5,u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f214,f59])).
% 0.21/0.53  fof(f214,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,u1_struct_0(sK0),u1_struct_0(sK0)),X1),k2_zfmisc_1(u1_struct_0(sK0),X2)) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,u1_orders_2(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f88,f36])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X1) | ~r2_hidden(X0,u1_orders_2(X1)) | ~r2_hidden(X2,X3) | r2_hidden(k4_tarski(sK8(X0,u1_struct_0(X1),u1_struct_0(X1)),X2),k2_zfmisc_1(u1_struct_0(X1),X3))) )),
% 0.21/0.53    inference(resolution,[],[f86,f61])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK8(X0,u1_struct_0(X1),u1_struct_0(X1)),u1_struct_0(X1)) | ~r2_hidden(X0,u1_orders_2(X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.53    inference(resolution,[],[f58,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,X3) | r2_hidden(sK8(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((r2_hidden(sK8(X0,X1,X2),X2) & r2_hidden(sK7(X0,X1,X2),X1) & k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f19,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) => (r2_hidden(sK8(X0,X1,X2),X2) & r2_hidden(sK7(X0,X1,X2),X1) & k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((? [X4,X5] : (r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) | ~r2_hidden(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => ~(! [X4,X5] : ~(r2_hidden(X5,X2) & r2_hidden(X4,X1) & k4_tarski(X4,X5) = X0) & r2_hidden(X0,X3)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK8(k4_tarski(sK2,sK3),u1_struct_0(sK0),u1_struct_0(sK0)),X0) | r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK0),X0)) | ~r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))) )),
% 0.21/0.53    inference(superposition,[],[f172,f204])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    k4_tarski(sK2,sK3) = k4_tarski(sK7(k4_tarski(sK2,sK3),u1_struct_0(sK0),u1_struct_0(sK0)),sK8(k4_tarski(sK2,sK3),u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f193,f121])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,u1_orders_2(sK0)) | k4_tarski(sK7(X0,u1_struct_0(sK0),u1_struct_0(sK0)),sK8(X0,u1_struct_0(sK0),u1_struct_0(sK0))) = X0) )),
% 0.21/0.53    inference(resolution,[],[f103,f36])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_orders_2(X1) | k4_tarski(sK7(X0,u1_struct_0(X1),u1_struct_0(X1)),sK8(X0,u1_struct_0(X1),u1_struct_0(X1))) = X0 | ~r2_hidden(X0,u1_orders_2(X1))) )),
% 0.21/0.53    inference(resolution,[],[f56,f50])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,X3) | k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK7(X0,u1_struct_0(sK0),u1_struct_0(sK0)),X1),k2_zfmisc_1(u1_struct_0(sK0),X2)) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,u1_orders_2(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f87,f36])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X1) | ~r2_hidden(X0,u1_orders_2(X1)) | ~r2_hidden(X2,X3) | r2_hidden(k4_tarski(sK7(X0,u1_struct_0(X1),u1_struct_0(X1)),X2),k2_zfmisc_1(u1_struct_0(X1),X3))) )),
% 0.21/0.53    inference(resolution,[],[f85,f61])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK7(X0,u1_struct_0(X1),u1_struct_0(X1)),u1_struct_0(X1)) | ~r2_hidden(X0,u1_orders_2(X1)) | ~l1_orders_2(X1)) )),
% 0.21/0.53    inference(resolution,[],[f57,f50])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r2_hidden(X0,X3) | r2_hidden(sK7(X0,X1,X2),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f643,plain,(
% 0.21/0.53    ~r2_hidden(sK3,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0))),
% 0.21/0.53    inference(resolution,[],[f641,f193])).
% 0.21/0.53  fof(f641,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(k4_tarski(sK2,X0),u1_orders_2(sK0)) | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0)) | ~r2_hidden(X0,u1_struct_0(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f626,f270])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    r2_hidden(sK1,u1_struct_0(sK0))),
% 0.21/0.53    inference(resolution,[],[f264,f59])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f262,f159])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    ~r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f261])).
% 0.21/0.53  fof(f261,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) | ~r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) | ~r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))),
% 0.21/0.53    inference(resolution,[],[f247,f235])).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK8(k4_tarski(sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),X0) | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),X0)) | ~r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))) )),
% 0.21/0.53    inference(superposition,[],[f172,f161])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    k4_tarski(sK1,sK2) = k4_tarski(sK7(k4_tarski(sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK0)),sK8(k4_tarski(sK1,sK2),u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.21/0.53    inference(resolution,[],[f159,f121])).
% 0.21/0.53  fof(f626,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,X0),u1_orders_2(sK0)) | ~r2_hidden(k4_tarski(sK2,X0),u1_orders_2(sK0)) | ~r2_hidden(X0,u1_struct_0(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f618,f269])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    r2_hidden(sK2,u1_struct_0(sK0))),
% 0.21/0.53    inference(resolution,[],[f264,f60])).
% 0.21/0.53  fof(f618,plain,(
% 0.21/0.53    ( ! [X3] : (~r2_hidden(sK2,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(sK2,X3),u1_orders_2(sK0)) | r2_hidden(k4_tarski(sK1,X3),u1_orders_2(sK0)) | ~r2_hidden(sK1,u1_struct_0(sK0)) | ~r2_hidden(X3,u1_struct_0(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f616,f159])).
% 0.21/0.53  fof(f616,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0)) | ~r2_hidden(X1,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X0,X2),u1_orders_2(sK0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(sK0)) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,u1_struct_0(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f516,f36])).
% 0.21/0.53  fof(f516,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(sK0) | ~r2_hidden(X1,u1_struct_0(sK0)) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0)) | r2_hidden(k4_tarski(X2,X0),u1_orders_2(sK0)) | ~r2_hidden(k4_tarski(X2,X1),u1_orders_2(sK0)) | ~r2_hidden(X0,u1_struct_0(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f257,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    v4_orders_2(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~r2_hidden(X2,u1_struct_0(sK0)) | ~r2_hidden(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(sK0)) | r2_hidden(k4_tarski(X0,X2),u1_orders_2(sK0)) | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | ~l1_orders_2(sK0)) )),
% 0.21/0.53    inference(resolution,[],[f108,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v4_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (((v4_orders_2(X0) | ~r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v4_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : ((v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => (v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r8_relat_2(u1_orders_2(sK0),X3) | ~r2_hidden(k4_tarski(X2,X0),u1_orders_2(sK0)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X3) | ~r2_hidden(X2,X3) | ~r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0)) | r2_hidden(k4_tarski(X2,X1),u1_orders_2(sK0))) )),
% 0.21/0.53    inference(resolution,[],[f43,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    v1_relat_1(u1_orders_2(sK0))),
% 0.21/0.53    inference(resolution,[],[f64,f36])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_orders_2(X0) | v1_relat_1(u1_orders_2(X0))) )),
% 0.21/0.53    inference(resolution,[],[f50,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X6,X0,X7,X5,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1) | ~r8_relat_2(X0,X1) | r2_hidden(k4_tarski(X5,X7),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f26,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(rectify,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => r2_hidden(k4_tarski(X2,X4),X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_2)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (32343)------------------------------
% 0.21/0.53  % (32343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (32343)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (32343)Memory used [KB]: 2174
% 0.21/0.53  % (32343)Time elapsed: 0.112 s
% 0.21/0.53  % (32343)------------------------------
% 0.21/0.53  % (32343)------------------------------
% 0.21/0.53  % (32338)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.53  % (32330)Success in time 0.179 s
%------------------------------------------------------------------------------
