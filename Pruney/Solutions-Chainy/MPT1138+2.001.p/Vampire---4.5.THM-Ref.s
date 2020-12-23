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
% DateTime   : Thu Dec  3 13:09:39 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 465 expanded)
%              Number of leaves         :   14 ( 188 expanded)
%              Depth                    :   21
%              Number of atoms          :  340 (3335 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(subsumption_resolution,[],[f126,f39])).

fof(f39,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    & r1_orders_2(sK0,sK2,sK3)
    & r1_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f28,f27,f26,f25])).

fof(f25,plain,
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

fof(f26,plain,
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

fof(f27,plain,
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

fof(f28,plain,
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

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f126,plain,(
    ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f125,f40])).

fof(f40,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f125,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f124,f42])).

fof(f42,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f124,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f121,f45])).

fof(f45,plain,(
    ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f121,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f120,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f120,plain,(
    r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f119,f95])).

fof(f95,plain,(
    r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f67,f92])).

fof(f92,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f89,f83])).

fof(f83,plain,(
    ~ v1_xboole_0(u1_orders_2(sK0)) ),
    inference(resolution,[],[f78,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f78,plain,(
    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f77,f39])).

fof(f77,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f76,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f74,f41])).

fof(f41,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f56,f43])).

fof(f43,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f89,plain,
    ( v1_xboole_0(u1_orders_2(sK0))
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f73,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f73,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f53,f39])).

fof(f53,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f67,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f119,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f118,f94])).

fof(f94,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f68,f92])).

fof(f68,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f41])).

fof(f118,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f112,f93])).

fof(f93,plain,(
    r2_hidden(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f69,f92])).

fof(f69,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f59,f42])).

fof(f112,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK0))
    | ~ r2_hidden(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0)) ),
    inference(resolution,[],[f107,f71])).

fof(f71,plain,(
    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f70,f39])).

fof(f70,plain,
    ( r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).

fof(f107,plain,(
    ! [X0] :
      ( ~ r8_relat_2(u1_orders_2(sK0),X0)
      | ~ r2_hidden(sK3,X0)
      | ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK1,X0)
      | r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f96,f78])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK0))
      | ~ r2_hidden(sK3,X1)
      | ~ r2_hidden(sK2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ r8_relat_2(u1_orders_2(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f87,f90])).

fof(f90,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f73,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK0))
      | ~ r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK0))
      | ~ r2_hidden(sK3,X1)
      | ~ r2_hidden(sK2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ r8_relat_2(u1_orders_2(sK0),X1)
      | ~ v1_relat_1(u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f81,f46])).

fof(f46,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(k4_tarski(X5,X7),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f81,plain,(
    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f79,f41])).

fof(f79,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f75,f42])).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:22:20 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.38  ipcrm: permission denied for id (1225392128)
% 0.13/0.38  ipcrm: permission denied for id (1226506241)
% 0.13/0.38  ipcrm: permission denied for id (1226571779)
% 0.13/0.38  ipcrm: permission denied for id (1226604548)
% 0.13/0.38  ipcrm: permission denied for id (1226637317)
% 0.13/0.38  ipcrm: permission denied for id (1226670086)
% 0.13/0.39  ipcrm: permission denied for id (1226735624)
% 0.13/0.39  ipcrm: permission denied for id (1225424905)
% 0.13/0.39  ipcrm: permission denied for id (1226768394)
% 0.13/0.39  ipcrm: permission denied for id (1225490443)
% 0.13/0.39  ipcrm: permission denied for id (1226833933)
% 0.13/0.39  ipcrm: permission denied for id (1226899471)
% 0.13/0.40  ipcrm: permission denied for id (1226932240)
% 0.13/0.40  ipcrm: permission denied for id (1226997778)
% 0.13/0.40  ipcrm: permission denied for id (1227030547)
% 0.13/0.40  ipcrm: permission denied for id (1227096085)
% 0.13/0.41  ipcrm: permission denied for id (1227292699)
% 0.13/0.41  ipcrm: permission denied for id (1225588764)
% 0.13/0.41  ipcrm: permission denied for id (1227358238)
% 0.13/0.41  ipcrm: permission denied for id (1227391007)
% 0.13/0.42  ipcrm: permission denied for id (1227489314)
% 0.13/0.42  ipcrm: permission denied for id (1225654309)
% 0.13/0.42  ipcrm: permission denied for id (1227587622)
% 0.21/0.43  ipcrm: permission denied for id (1227751467)
% 0.21/0.43  ipcrm: permission denied for id (1227849774)
% 0.21/0.43  ipcrm: permission denied for id (1225687090)
% 0.21/0.44  ipcrm: permission denied for id (1225719859)
% 0.21/0.44  ipcrm: permission denied for id (1228046390)
% 0.21/0.44  ipcrm: permission denied for id (1228111928)
% 0.21/0.44  ipcrm: permission denied for id (1225752634)
% 0.21/0.44  ipcrm: permission denied for id (1225785403)
% 0.21/0.45  ipcrm: permission denied for id (1225818175)
% 0.21/0.45  ipcrm: permission denied for id (1225850945)
% 0.21/0.46  ipcrm: permission denied for id (1228406853)
% 0.21/0.46  ipcrm: permission denied for id (1228472391)
% 0.21/0.46  ipcrm: permission denied for id (1228570698)
% 0.21/0.47  ipcrm: permission denied for id (1228701774)
% 0.21/0.47  ipcrm: permission denied for id (1228734543)
% 0.21/0.47  ipcrm: permission denied for id (1228800081)
% 0.21/0.47  ipcrm: permission denied for id (1225982036)
% 0.21/0.48  ipcrm: permission denied for id (1228963927)
% 0.21/0.48  ipcrm: permission denied for id (1228996696)
% 0.21/0.48  ipcrm: permission denied for id (1229029465)
% 0.21/0.48  ipcrm: permission denied for id (1229062234)
% 0.21/0.48  ipcrm: permission denied for id (1229095003)
% 0.21/0.49  ipcrm: permission denied for id (1229226079)
% 0.21/0.49  ipcrm: permission denied for id (1229357155)
% 0.21/0.49  ipcrm: permission denied for id (1229389924)
% 0.21/0.50  ipcrm: permission denied for id (1229553769)
% 0.21/0.50  ipcrm: permission denied for id (1229586538)
% 0.21/0.50  ipcrm: permission denied for id (1226178667)
% 0.21/0.50  ipcrm: permission denied for id (1229619308)
% 0.21/0.50  ipcrm: permission denied for id (1229684846)
% 0.21/0.50  ipcrm: permission denied for id (1229717615)
% 0.21/0.51  ipcrm: permission denied for id (1226244208)
% 0.21/0.51  ipcrm: permission denied for id (1226276977)
% 0.21/0.51  ipcrm: permission denied for id (1229750386)
% 0.21/0.51  ipcrm: permission denied for id (1229783155)
% 0.21/0.51  ipcrm: permission denied for id (1226342516)
% 0.21/0.51  ipcrm: permission denied for id (1229914232)
% 0.21/0.52  ipcrm: permission denied for id (1229947001)
% 0.21/0.52  ipcrm: permission denied for id (1230012539)
% 0.21/0.52  ipcrm: permission denied for id (1230045308)
% 0.21/0.52  ipcrm: permission denied for id (1226440829)
% 0.21/0.52  ipcrm: permission denied for id (1226473599)
% 0.56/0.59  % (23913)WARNING: option uwaf not known.
% 0.56/0.59  % (23913)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.56/0.59  % (23913)Refutation found. Thanks to Tanya!
% 0.56/0.59  % SZS status Theorem for theBenchmark
% 0.56/0.59  % SZS output start Proof for theBenchmark
% 0.56/0.59  fof(f127,plain,(
% 0.56/0.59    $false),
% 0.56/0.59    inference(subsumption_resolution,[],[f126,f39])).
% 0.56/0.59  fof(f39,plain,(
% 0.56/0.59    l1_orders_2(sK0)),
% 0.56/0.59    inference(cnf_transformation,[],[f29])).
% 0.56/0.59  fof(f29,plain,(
% 0.56/0.59    (((~r1_orders_2(sK0,sK1,sK3) & r1_orders_2(sK0,sK2,sK3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v4_orders_2(sK0)),
% 0.56/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f28,f27,f26,f25])).
% 0.56/0.59  fof(f25,plain,(
% 0.56/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(sK0,X1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v4_orders_2(sK0))),
% 0.56/0.59    introduced(choice_axiom,[])).
% 0.56/0.59  fof(f26,plain,(
% 0.56/0.59    ? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(sK0,X1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,X1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.56/0.59    introduced(choice_axiom,[])).
% 0.56/0.59  fof(f27,plain,(
% 0.56/0.59    ? [X2] : (? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,X2,X3) & r1_orders_2(sK0,sK1,X2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,sK2,X3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.56/0.59    introduced(choice_axiom,[])).
% 0.56/0.59  fof(f28,plain,(
% 0.56/0.59    ? [X3] : (~r1_orders_2(sK0,sK1,X3) & r1_orders_2(sK0,sK2,X3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(X3,u1_struct_0(sK0))) => (~r1_orders_2(sK0,sK1,sK3) & r1_orders_2(sK0,sK2,sK3) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(sK3,u1_struct_0(sK0)))),
% 0.56/0.59    introduced(choice_axiom,[])).
% 0.56/0.59  fof(f13,plain,(
% 0.56/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_orders_2(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 0.56/0.59    inference(flattening,[],[f12])).
% 0.56/0.59  fof(f12,plain,(
% 0.56/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_orders_2(X0,X1,X3) & (r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 0.56/0.59    inference(ennf_transformation,[],[f11])).
% 0.56/0.59  fof(f11,negated_conjecture,(
% 0.56/0.59    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.56/0.59    inference(negated_conjecture,[],[f10])).
% 0.56/0.59  fof(f10,conjecture,(
% 0.56/0.59    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).
% 0.56/0.59  fof(f126,plain,(
% 0.56/0.59    ~l1_orders_2(sK0)),
% 0.56/0.59    inference(subsumption_resolution,[],[f125,f40])).
% 0.56/0.59  fof(f40,plain,(
% 0.56/0.59    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.56/0.59    inference(cnf_transformation,[],[f29])).
% 0.56/0.59  fof(f125,plain,(
% 0.56/0.59    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.56/0.59    inference(subsumption_resolution,[],[f124,f42])).
% 0.56/0.59  fof(f42,plain,(
% 0.56/0.59    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.56/0.59    inference(cnf_transformation,[],[f29])).
% 0.56/0.59  fof(f124,plain,(
% 0.56/0.59    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.56/0.59    inference(subsumption_resolution,[],[f121,f45])).
% 0.56/0.59  fof(f45,plain,(
% 0.56/0.59    ~r1_orders_2(sK0,sK1,sK3)),
% 0.56/0.59    inference(cnf_transformation,[],[f29])).
% 0.56/0.59  fof(f121,plain,(
% 0.56/0.59    r1_orders_2(sK0,sK1,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.56/0.59    inference(resolution,[],[f120,f57])).
% 0.56/0.59  fof(f57,plain,(
% 0.56/0.59    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.56/0.59    inference(cnf_transformation,[],[f35])).
% 0.56/0.59  fof(f35,plain,(
% 0.56/0.59    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.56/0.59    inference(nnf_transformation,[],[f18])).
% 0.56/0.59  fof(f18,plain,(
% 0.56/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.56/0.59    inference(ennf_transformation,[],[f8])).
% 0.56/0.59  fof(f8,axiom,(
% 0.56/0.59    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.56/0.59  fof(f120,plain,(
% 0.56/0.59    r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0))),
% 0.56/0.59    inference(subsumption_resolution,[],[f119,f95])).
% 0.56/0.59  fof(f95,plain,(
% 0.56/0.59    r2_hidden(sK1,u1_struct_0(sK0))),
% 0.56/0.59    inference(subsumption_resolution,[],[f67,f92])).
% 0.56/0.59  fof(f92,plain,(
% 0.56/0.59    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.56/0.59    inference(subsumption_resolution,[],[f89,f83])).
% 0.56/0.59  fof(f83,plain,(
% 0.56/0.59    ~v1_xboole_0(u1_orders_2(sK0))),
% 0.56/0.59    inference(resolution,[],[f78,f60])).
% 0.56/0.59  fof(f60,plain,(
% 0.56/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 0.56/0.59    inference(cnf_transformation,[],[f22])).
% 0.56/0.59  fof(f22,plain,(
% 0.56/0.59    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.56/0.59    inference(ennf_transformation,[],[f1])).
% 0.56/0.59  fof(f1,axiom,(
% 0.56/0.59    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.56/0.59  fof(f78,plain,(
% 0.56/0.59    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))),
% 0.56/0.59    inference(subsumption_resolution,[],[f77,f39])).
% 0.56/0.59  fof(f77,plain,(
% 0.56/0.59    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) | ~l1_orders_2(sK0)),
% 0.56/0.59    inference(subsumption_resolution,[],[f76,f40])).
% 0.56/0.59  fof(f76,plain,(
% 0.56/0.59    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.56/0.59    inference(subsumption_resolution,[],[f74,f41])).
% 0.56/0.59  fof(f41,plain,(
% 0.56/0.59    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.56/0.59    inference(cnf_transformation,[],[f29])).
% 0.56/0.59  fof(f74,plain,(
% 0.56/0.59    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.56/0.59    inference(resolution,[],[f56,f43])).
% 0.56/0.59  fof(f43,plain,(
% 0.56/0.59    r1_orders_2(sK0,sK1,sK2)),
% 0.56/0.59    inference(cnf_transformation,[],[f29])).
% 0.56/0.59  fof(f56,plain,(
% 0.56/0.59    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.56/0.59    inference(cnf_transformation,[],[f35])).
% 0.56/0.59  fof(f89,plain,(
% 0.56/0.59    v1_xboole_0(u1_orders_2(sK0)) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.56/0.59    inference(resolution,[],[f73,f58])).
% 0.56/0.59  fof(f58,plain,(
% 0.56/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.56/0.59    inference(cnf_transformation,[],[f19])).
% 0.56/0.59  fof(f19,plain,(
% 0.56/0.59    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.56/0.59    inference(ennf_transformation,[],[f5])).
% 0.56/0.59  fof(f5,axiom,(
% 0.56/0.59    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.56/0.59  fof(f73,plain,(
% 0.56/0.59    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))),
% 0.56/0.59    inference(resolution,[],[f53,f39])).
% 0.75/0.59  fof(f53,plain,(
% 0.75/0.59    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))) )),
% 0.75/0.59    inference(cnf_transformation,[],[f16])).
% 0.75/0.59  fof(f16,plain,(
% 0.75/0.59    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.75/0.59    inference(ennf_transformation,[],[f9])).
% 0.75/0.59  fof(f9,axiom,(
% 0.75/0.59    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.75/0.59  fof(f67,plain,(
% 0.75/0.59    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0))),
% 0.75/0.59    inference(resolution,[],[f59,f40])).
% 0.75/0.59  fof(f59,plain,(
% 0.75/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.75/0.59    inference(cnf_transformation,[],[f21])).
% 0.75/0.59  fof(f21,plain,(
% 0.75/0.59    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.75/0.59    inference(flattening,[],[f20])).
% 0.75/0.59  fof(f20,plain,(
% 0.75/0.59    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.75/0.59    inference(ennf_transformation,[],[f3])).
% 0.75/0.59  fof(f3,axiom,(
% 0.75/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.75/0.59  fof(f119,plain,(
% 0.75/0.59    ~r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0))),
% 0.75/0.59    inference(subsumption_resolution,[],[f118,f94])).
% 0.75/0.59  fof(f94,plain,(
% 0.75/0.59    r2_hidden(sK2,u1_struct_0(sK0))),
% 0.75/0.59    inference(subsumption_resolution,[],[f68,f92])).
% 0.75/0.59  fof(f68,plain,(
% 0.75/0.59    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK2,u1_struct_0(sK0))),
% 0.75/0.59    inference(resolution,[],[f59,f41])).
% 0.75/0.59  fof(f118,plain,(
% 0.75/0.59    ~r2_hidden(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0))),
% 0.75/0.59    inference(subsumption_resolution,[],[f112,f93])).
% 0.75/0.59  fof(f93,plain,(
% 0.75/0.59    r2_hidden(sK3,u1_struct_0(sK0))),
% 0.75/0.59    inference(subsumption_resolution,[],[f69,f92])).
% 0.75/0.59  fof(f69,plain,(
% 0.75/0.59    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK3,u1_struct_0(sK0))),
% 0.75/0.59    inference(resolution,[],[f59,f42])).
% 0.75/0.59  fof(f112,plain,(
% 0.75/0.59    ~r2_hidden(sK3,u1_struct_0(sK0)) | ~r2_hidden(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK1,u1_struct_0(sK0)) | r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0))),
% 0.75/0.59    inference(resolution,[],[f107,f71])).
% 0.75/0.59  fof(f71,plain,(
% 0.75/0.59    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))),
% 0.75/0.59    inference(subsumption_resolution,[],[f70,f39])).
% 0.75/0.59  fof(f70,plain,(
% 0.75/0.59    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.75/0.59    inference(resolution,[],[f54,f38])).
% 0.75/0.59  fof(f38,plain,(
% 0.75/0.59    v4_orders_2(sK0)),
% 0.75/0.59    inference(cnf_transformation,[],[f29])).
% 0.75/0.59  fof(f54,plain,(
% 0.75/0.59    ( ! [X0] : (~v4_orders_2(X0) | r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.75/0.59    inference(cnf_transformation,[],[f34])).
% 0.75/0.59  fof(f34,plain,(
% 0.75/0.59    ! [X0] : (((v4_orders_2(X0) | ~r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v4_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.75/0.59    inference(nnf_transformation,[],[f17])).
% 0.75/0.59  fof(f17,plain,(
% 0.75/0.59    ! [X0] : ((v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.75/0.59    inference(ennf_transformation,[],[f7])).
% 0.75/0.59  fof(f7,axiom,(
% 0.75/0.59    ! [X0] : (l1_orders_2(X0) => (v4_orders_2(X0) <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_orders_2)).
% 0.75/0.59  fof(f107,plain,(
% 0.75/0.59    ( ! [X0] : (~r8_relat_2(u1_orders_2(sK0),X0) | ~r2_hidden(sK3,X0) | ~r2_hidden(sK2,X0) | ~r2_hidden(sK1,X0) | r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0))) )),
% 0.75/0.59    inference(resolution,[],[f96,f78])).
% 0.75/0.59  fof(f96,plain,(
% 0.75/0.59    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK0)) | r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK0)) | ~r2_hidden(sK3,X1) | ~r2_hidden(sK2,X1) | ~r2_hidden(X0,X1) | ~r8_relat_2(u1_orders_2(sK0),X1)) )),
% 0.75/0.59    inference(subsumption_resolution,[],[f87,f90])).
% 0.75/0.59  fof(f90,plain,(
% 0.75/0.59    v1_relat_1(u1_orders_2(sK0))),
% 0.75/0.59    inference(resolution,[],[f73,f63])).
% 0.75/0.59  fof(f63,plain,(
% 0.75/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.75/0.59    inference(cnf_transformation,[],[f24])).
% 0.75/0.59  fof(f24,plain,(
% 0.75/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.75/0.59    inference(ennf_transformation,[],[f4])).
% 0.75/0.59  fof(f4,axiom,(
% 0.75/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.75/0.59  fof(f87,plain,(
% 0.75/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK0)) | ~r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK0)) | ~r2_hidden(sK3,X1) | ~r2_hidden(sK2,X1) | ~r2_hidden(X0,X1) | ~r8_relat_2(u1_orders_2(sK0),X1) | ~v1_relat_1(u1_orders_2(sK0))) )),
% 0.75/0.59    inference(resolution,[],[f81,f46])).
% 0.75/0.59  fof(f46,plain,(
% 0.75/0.59    ( ! [X6,X0,X7,X5,X1] : (~r2_hidden(k4_tarski(X6,X7),X0) | r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1) | ~r8_relat_2(X0,X1) | ~v1_relat_1(X0)) )),
% 0.75/0.59    inference(cnf_transformation,[],[f33])).
% 0.75/0.59  fof(f33,plain,(
% 0.75/0.59    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | (~r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.75/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f32])).
% 0.75/0.59  fof(f32,plain,(
% 0.75/0.59    ! [X1,X0] : (? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (~r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)))),
% 0.75/0.59    introduced(choice_axiom,[])).
% 0.75/0.59  fof(f31,plain,(
% 0.75/0.59    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X5,X6,X7] : (r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~r2_hidden(k4_tarski(X5,X6),X0) | ~r2_hidden(X7,X1) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.75/0.59    inference(rectify,[],[f30])).
% 0.75/0.59  fof(f30,plain,(
% 0.75/0.59    ! [X0] : (! [X1] : ((r8_relat_2(X0,X1) | ? [X2,X3,X4] : (~r2_hidden(k4_tarski(X2,X4),X0) & r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~r8_relat_2(X0,X1))) | ~v1_relat_1(X0))),
% 0.75/0.59    inference(nnf_transformation,[],[f15])).
% 0.75/0.59  fof(f15,plain,(
% 0.75/0.59    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.75/0.59    inference(flattening,[],[f14])).
% 0.75/0.59  fof(f14,plain,(
% 0.75/0.59    ! [X0] : (! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : (r2_hidden(k4_tarski(X2,X4),X0) | (~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X4,X1) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.75/0.59    inference(ennf_transformation,[],[f6])).
% 0.75/0.59  fof(f6,axiom,(
% 0.75/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r8_relat_2(X0,X1) <=> ! [X2,X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X4,X1) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => r2_hidden(k4_tarski(X2,X4),X0))))),
% 0.75/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_2)).
% 0.75/0.59  fof(f81,plain,(
% 0.75/0.59    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))),
% 0.75/0.59    inference(subsumption_resolution,[],[f80,f39])).
% 0.75/0.59  fof(f80,plain,(
% 0.75/0.59    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) | ~l1_orders_2(sK0)),
% 0.75/0.59    inference(subsumption_resolution,[],[f79,f41])).
% 0.75/0.59  fof(f79,plain,(
% 0.75/0.59    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.75/0.59    inference(subsumption_resolution,[],[f75,f42])).
% 0.75/0.59  fof(f75,plain,(
% 0.75/0.59    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0)),
% 0.75/0.59    inference(resolution,[],[f56,f44])).
% 0.75/0.59  fof(f44,plain,(
% 0.75/0.59    r1_orders_2(sK0,sK2,sK3)),
% 0.75/0.59    inference(cnf_transformation,[],[f29])).
% 0.75/0.59  % SZS output end Proof for theBenchmark
% 0.75/0.59  % (23913)------------------------------
% 0.75/0.59  % (23913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.75/0.59  % (23913)Termination reason: Refutation
% 0.75/0.59  
% 0.75/0.59  % (23913)Memory used [KB]: 1023
% 0.75/0.59  % (23913)Time elapsed: 0.006 s
% 0.75/0.59  % (23913)------------------------------
% 0.75/0.59  % (23913)------------------------------
% 0.75/0.59  % (23767)Success in time 0.225 s
%------------------------------------------------------------------------------
