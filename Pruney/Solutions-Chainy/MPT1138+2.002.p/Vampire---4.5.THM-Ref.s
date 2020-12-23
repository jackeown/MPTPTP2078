%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 392 expanded)
%              Number of leaves         :   13 ( 170 expanded)
%              Depth                    :   10
%              Number of atoms          :  277 (2973 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(subsumption_resolution,[],[f105,f93])).

fof(f93,plain,(
    r2_hidden(sK3,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f73,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f73,plain,(
    r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f59,f62,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f62,plain,(
    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f35,f38,f36,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f36,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    & r1_orders_2(sK0,sK2,sK3)
    & r1_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f22,f21,f20,f19])).

fof(f19,plain,
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

fof(f20,plain,
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

fof(f21,plain,
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

fof(f22,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(f38,plain,(
    r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f35,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f33,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f33,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f105,plain,(
    ~ r2_hidden(sK3,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f60,f77,f57,f62,f61,f66,f78,f40])).

fof(f40,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(k4_tarski(X5,X7),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f26])).

fof(f26,plain,(
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
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

fof(f78,plain,(
    r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f59,f61,f52])).

fof(f66,plain,(
    ~ r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f34,f39,f36,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f34,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f34,f37,f35,f50])).

fof(f37,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f33,f32,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).

fof(f32,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f55])).

fof(f60,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(unit_resulting_resolution,[],[f59,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (17056)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (17065)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.47  % (17057)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.21/0.48  % (17061)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.48  % (17064)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  % (17064)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    r2_hidden(sK3,u1_struct_0(sK0))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f73,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.48    inference(flattening,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK2,sK3),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f59,f62,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f33,f35,f38,f36,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    (((~r1_orders_2(sK0,sK1,sK3) & r1_orders_2(sK0,sK2,sK3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v4_orders_2(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f22,f21,f20,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(sK0,X1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v4_orders_2(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(sK0,X1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X2] : (? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,sK2,X3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,sK2,X3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r1_orders_2(sK0,sK1,sK3) & r1_orders_2(sK0,sK2,sK3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_orders_2(X0,X1,X3) & (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    r1_orders_2(sK0,sK2,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    l1_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f33,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ~r2_hidden(sK3,u1_struct_0(sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f60,f77,f57,f62,f61,f66,f78,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X6,X0,X7,X5,X1] : (~r2_hidden(k4_tarski(X6,X7),X0) | r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1) | ~r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f25,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(rectify,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => r2_hidden(k4_tarski(X2,X4),X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    r2_hidden(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f65,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f59,f61,f52])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ~r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f33,f34,f39,f36,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ~r1_orders_2(sK0,sK1,sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f33,f34,f37,f35,f50])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    r1_orders_2(sK0,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f33,f32,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (~v4_orders_2(X0) | r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (((v4_orders_2(X0) | ~r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v4_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : ((v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_orders_2(X0) => (v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v4_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    r2_hidden(sK2,u1_struct_0(sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f65,f55])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    v1_relat_1(u1_orders_2(sK0))),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f59,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (17064)------------------------------
% 0.21/0.49  % (17064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (17064)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (17064)Memory used [KB]: 5500
% 0.21/0.49  % (17064)Time elapsed: 0.076 s
% 0.21/0.49  % (17064)------------------------------
% 0.21/0.49  % (17064)------------------------------
% 0.21/0.49  % (17047)Success in time 0.131 s
%------------------------------------------------------------------------------
