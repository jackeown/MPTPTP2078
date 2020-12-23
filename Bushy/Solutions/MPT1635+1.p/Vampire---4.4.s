%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t15_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:44 EDT 2019

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 609 expanded)
%              Number of leaves         :   14 ( 187 expanded)
%              Depth                    :   26
%              Number of atoms          :  594 (3369 expanded)
%              Number of equality atoms :   45 ( 537 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6596,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6569,f6514])).

fof(f6514,plain,(
    ~ r2_hidden(sK2(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f6496,f65])).

fof(f65,plain,(
    k4_waybel_0(sK0,sK1) != a_2_1_waybel_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k4_waybel_0(sK0,sK1) != a_2_1_waybel_0(sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_waybel_0(X0,X1) != a_2_1_waybel_0(X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k4_waybel_0(sK0,X1) != a_2_1_waybel_0(sK0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k4_waybel_0(X0,X1) != a_2_1_waybel_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k4_waybel_0(X0,sK1) != a_2_1_waybel_0(X0,sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_waybel_0(X0,X1) != a_2_1_waybel_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_waybel_0(X0,X1) != a_2_1_waybel_0(X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t15_waybel_0.p',t15_waybel_0)).

fof(f6496,plain,
    ( ~ r2_hidden(sK2(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,sK1) ),
    inference(factoring,[],[f4673])).

fof(f4673,plain,(
    ! [X35] :
      ( ~ r2_hidden(sK2(X35,a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
      | ~ r2_hidden(sK2(X35,a_2_1_waybel_0(sK0,sK1)),X35)
      | a_2_1_waybel_0(sK0,sK1) = X35 ) ),
    inference(resolution,[],[f4634,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK2(X0,X1),X1)
      | ~ r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t15_waybel_0.p',t2_tarski)).

fof(f4634,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f4633,f64])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f4633,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f4619])).

fof(f4619,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f1137,f127])).

fof(f127,plain,(
    ! [X28,X29] :
      ( r2_hidden(sK9(sK0,X28,X29),X28)
      | ~ r2_hidden(X29,k4_waybel_0(sK0,X28))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f126,f112])).

fof(f112,plain,(
    ! [X10] :
      ( m1_subset_1(k4_waybel_0(sK0,X10),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f63,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t15_waybel_0.p',dt_k4_waybel_0)).

fof(f63,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f126,plain,(
    ! [X28,X29] :
      ( r2_hidden(sK9(sK0,X28,X29),X28)
      | ~ r2_hidden(X29,k4_waybel_0(sK0,X28))
      | ~ m1_subset_1(k4_waybel_0(sK0,X28),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f120,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t15_waybel_0.p',t4_subset)).

fof(f120,plain,(
    ! [X28,X29] :
      ( r2_hidden(sK9(sK0,X28,X29),X28)
      | ~ r2_hidden(X29,k4_waybel_0(sK0,X28))
      | ~ m1_subset_1(X29,u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_0(sK0,X28),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f63,f91])).

fof(f91,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ( ( ! [X4] :
                          ( ~ r2_hidden(X4,X1)
                          | ~ r1_orders_2(X0,X4,sK7(X0,X1,X2))
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(sK7(X0,X1,X2),X2) )
                    & ( ( r2_hidden(sK8(X0,X1,X2),X1)
                        & r1_orders_2(X0,sK8(X0,X1,X2),sK7(X0,X1,X2))
                        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) )
                      | r2_hidden(sK7(X0,X1,X2),X2) )
                    & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X7,X6)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ( r2_hidden(sK9(X0,X1,X6),X1)
                            & r1_orders_2(X0,sK9(X0,X1,X6),X6)
                            & m1_subset_1(sK9(X0,X1,X6),u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9])],[f57,f60,f59,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r1_orders_2(X0,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r1_orders_2(X0,X5,X3)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r1_orders_2(X0,X4,sK7(X0,X1,X2))
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r1_orders_2(X0,X5,sK7(X0,X1,X2))
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | r2_hidden(sK7(X0,X1,X2),X2) )
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r1_orders_2(X0,X5,X3)
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r1_orders_2(X0,sK8(X0,X1,X2),X3)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r1_orders_2(X0,X8,X6)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( r2_hidden(sK9(X0,X1,X6),X1)
        & r1_orders_2(X0,sK9(X0,X1,X6),X6)
        & m1_subset_1(sK9(X0,X1,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X4,X3)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r1_orders_2(X0,X5,X3)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X7,X6)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ? [X8] :
                              ( r2_hidden(X8,X1)
                              & r1_orders_2(X0,X8,X6)
                              & m1_subset_1(X8,u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X4,X3)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X4,X3)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X4,X3)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X4,X3)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X4,X3)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X4,X3)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X4,X3)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X4,X3)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t15_waybel_0.p',d16_waybel_0)).

fof(f1137,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK9(sK0,sK1,X2),X3)
      | r2_hidden(X2,a_2_1_waybel_0(sK0,X3))
      | ~ r2_hidden(X2,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1136,f225])).

fof(f225,plain,(
    ! [X29] :
      ( m1_subset_1(X29,u1_struct_0(sK0))
      | ~ r2_hidden(X29,k4_waybel_0(sK0,sK1)) ) ),
    inference(resolution,[],[f164,f77])).

fof(f164,plain,(
    m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f137,f63])).

fof(f137,plain,
    ( m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f64,f74])).

fof(f1136,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,a_2_1_waybel_0(sK0,X3))
      | ~ r2_hidden(sK9(sK0,sK1,X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1135,f77])).

fof(f1135,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,a_2_1_waybel_0(sK0,X3))
      | ~ r2_hidden(sK9(sK0,sK1,X2),X3)
      | ~ m1_subset_1(sK9(sK0,sK1,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1134,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f1134,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,a_2_1_waybel_0(sK0,X3))
      | ~ r2_hidden(sK9(sK0,sK1,X2),X3)
      | ~ m1_subset_1(sK9(sK0,sK1,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f1128,f63])).

fof(f1128,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,a_2_1_waybel_0(sK0,X3))
      | ~ r2_hidden(sK9(sK0,sK1,X2),X3)
      | ~ m1_subset_1(sK9(sK0,sK1,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f1126])).

fof(f1126,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,a_2_1_waybel_0(sK0,X3))
      | ~ r2_hidden(sK9(sK0,sK1,X2),X3)
      | ~ m1_subset_1(sK9(sK0,sK1,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f183,f89])).

fof(f89,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(X3,a_2_1_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ r2_hidden(X4,X2)
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X2)
            & r1_orders_2(X1,sK4(X0,X1,X2),sK3(X0,X1,X2))
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
            & sK3(X0,X1,X2) = X0
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X2)
              & r1_orders_2(X1,X6,X5)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X2)
            & r1_orders_2(X1,X6,sK3(X0,X1,X2))
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK3(X0,X1,X2) = X0
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X2)
          & r1_orders_2(X1,X6,X5)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK4(X0,X1,X2),X2)
        & r1_orders_2(X1,sK4(X0,X1,X2),X5)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ? [X6] :
                  ( r2_hidden(X6,X2)
                  & r1_orders_2(X1,X6,X5)
                  & m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ! [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r1_orders_2(X1,X4,X3)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r1_orders_2(X1,X4,X3)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t15_waybel_0.p',fraenkel_a_2_1_waybel_0)).

fof(f183,plain,(
    ! [X22] :
      ( r1_orders_2(sK0,sK9(sK0,sK1,X22),X22)
      | ~ r2_hidden(X22,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X22,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f182,f63])).

fof(f182,plain,(
    ! [X22] :
      ( r1_orders_2(sK0,sK9(sK0,sK1,X22),X22)
      | ~ r2_hidden(X22,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f151,f164])).

fof(f151,plain,(
    ! [X22] :
      ( r1_orders_2(sK0,sK9(sK0,sK1,X22),X22)
      | ~ r2_hidden(X22,k4_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X22,u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f64,f92])).

fof(f92,plain,(
    ! [X6,X0,X1] :
      ( r1_orders_2(X0,sK9(X0,X1,X6),X6)
      | ~ r2_hidden(X6,k4_waybel_0(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,sK9(X0,X1,X6),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f6569,plain,(
    r2_hidden(sK2(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f6538,f5616])).

fof(f5616,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | r2_hidden(X0,k4_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f5615,f64])).

fof(f5615,plain,(
    ! [X0] :
      ( r2_hidden(X0,k4_waybel_0(sK0,sK1))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f5599])).

fof(f5599,plain,(
    ! [X0] :
      ( r2_hidden(X0,k4_waybel_0(sK0,sK1))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f805,f104])).

fof(f104,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK4(X8,sK0,X9),X9)
      | ~ r2_hidden(X8,a_2_1_waybel_0(sK0,X9))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f98,f63])).

fof(f98,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK4(X8,sK0,X9),X9)
      | ~ r2_hidden(X8,a_2_1_waybel_0(sK0,X9))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f62,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f805,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,sK0,sK1),X1)
      | r2_hidden(X0,k4_waybel_0(sK0,X1))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f804,f112])).

fof(f804,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | r2_hidden(X0,k4_waybel_0(sK0,X1))
      | ~ r2_hidden(sK4(X0,sK0,sK1),X1)
      | ~ m1_subset_1(k4_waybel_0(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f803,f562])).

fof(f562,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f561,f62])).

fof(f561,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f560,f63])).

fof(f560,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f553,f64])).

fof(f553,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f552])).

fof(f552,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f155,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f155,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0,sK0,sK1),u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f154,f62])).

fof(f154,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0,sK0,sK1),u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f132,f63])).

fof(f132,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0,sK0,sK1),u1_struct_0(sK0))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f64,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f803,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | r2_hidden(X0,k4_waybel_0(sK0,X1))
      | ~ r2_hidden(sK4(X0,sK0,sK1),X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_0(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f802,f77])).

fof(f802,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | r2_hidden(X0,k4_waybel_0(sK0,X1))
      | ~ r2_hidden(sK4(X0,sK0,sK1),X1)
      | ~ m1_subset_1(sK4(X0,sK0,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_0(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f799,f63])).

fof(f799,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | r2_hidden(X0,k4_waybel_0(sK0,X1))
      | ~ r2_hidden(sK4(X0,sK0,sK1),X1)
      | ~ m1_subset_1(sK4(X0,sK0,sK1),u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k4_waybel_0(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f798,f90])).

fof(f90,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k4_waybel_0(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X7,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X7,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f798,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK4(X0,sK0,sK1),X0)
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f797,f62])).

fof(f797,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK4(X0,sK0,sK1),X0)
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f796,f63])).

fof(f796,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK4(X0,sK0,sK1),X0)
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f787,f64])).

fof(f787,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK4(X0,sK0,sK1),X0)
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f786])).

fof(f786,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,sK4(X0,sK0,sK1),X0)
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ r2_hidden(X0,a_2_1_waybel_0(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f161,f69])).

fof(f161,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK4(X3,sK0,sK1),sK3(X3,sK0,sK1))
      | ~ r2_hidden(X3,a_2_1_waybel_0(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f160,f62])).

fof(f160,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK4(X3,sK0,sK1),sK3(X3,sK0,sK1))
      | ~ r2_hidden(X3,a_2_1_waybel_0(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f135,f63])).

fof(f135,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK4(X3,sK0,sK1),sK3(X3,sK0,sK1))
      | ~ r2_hidden(X3,a_2_1_waybel_0(sK0,sK1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f64,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK4(X0,X1,X2),sK3(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6538,plain,(
    r2_hidden(sK2(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),a_2_1_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f6527,f65])).

fof(f6527,plain,
    ( k4_waybel_0(sK0,sK1) = a_2_1_waybel_0(sK0,sK1)
    | r2_hidden(sK2(k4_waybel_0(sK0,sK1),a_2_1_waybel_0(sK0,sK1)),a_2_1_waybel_0(sK0,sK1)) ),
    inference(resolution,[],[f6514,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK2(X0,X1),X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
