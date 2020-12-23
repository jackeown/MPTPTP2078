%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t29_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:48 EDT 2019

% Result     : Theorem 182.98s
% Output     : Refutation 182.98s
% Verified   : 
% Statistics : Number of formulae       :  154 (1405 expanded)
%              Number of leaves         :   18 ( 497 expanded)
%              Depth                    :   20
%              Number of atoms          :  654 (9675 expanded)
%              Number of equality atoms :   42 ( 253 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44226,plain,(
    $false ),
    inference(subsumption_resolution,[],[f44225,f3991])).

fof(f3991,plain,(
    ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f3983,f169])).

fof(f169,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,
    ( ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      | ~ v13_waybel_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) )
    & v13_waybel_0(sK2,sK0)
    & v13_waybel_0(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f71,f123,f122,f121])).

fof(f121,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                  | ~ v13_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
                & v13_waybel_0(X2,X0)
                & v13_waybel_0(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
                | ~ v13_waybel_0(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) )
              & v13_waybel_0(X2,sK0)
              & v13_waybel_0(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f122,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v13_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v13_waybel_0(X2,X0)
              & v13_waybel_0(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(X0),sK1,X2),X0)
              | ~ v13_waybel_0(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) )
            & v13_waybel_0(X2,X0)
            & v13_waybel_0(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
            | ~ v13_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
          & v13_waybel_0(X2,X0)
          & v13_waybel_0(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(X0),X1,sK2),X0)
          | ~ v13_waybel_0(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) )
        & v13_waybel_0(sK2,X0)
        & v13_waybel_0(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v13_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v13_waybel_0(X2,X0)
              & v13_waybel_0(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                | ~ v13_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) )
              & v13_waybel_0(X2,X0)
              & v13_waybel_0(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v13_waybel_0(X2,X0)
                    & v13_waybel_0(X1,X0) )
                 => ( v13_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                    & v13_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v13_waybel_0(X2,X0)
                  & v13_waybel_0(X1,X0) )
               => ( v13_waybel_0(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                  & v13_waybel_0(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',t29_waybel_0)).

fof(f3983,plain,
    ( ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f1457,f990])).

fof(f990,plain,(
    ! [X3] :
      ( m1_subset_1(k2_xboole_0(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f982,f168])).

fof(f168,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f124])).

fof(f982,plain,(
    ! [X3] :
      ( m1_subset_1(k2_xboole_0(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f981])).

fof(f981,plain,(
    ! [X3] :
      ( m1_subset_1(k2_xboole_0(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f312,f237])).

fof(f237,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f116])).

fof(f116,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',redefinition_k4_subset_1)).

fof(f312,plain,(
    ! [X9] :
      ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,X9),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f168,f236])).

fof(f236,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f115])).

fof(f115,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f114])).

fof(f114,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',dt_k4_subset_1)).

fof(f1457,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(global_subsumption,[],[f1392,f1451,f1453])).

fof(f1453,plain,
    ( ~ r2_hidden(sK6(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1452,f1077])).

fof(f1077,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f1072,f1053])).

fof(f1053,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f314,f169])).

fof(f314,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK1,X11) = k2_xboole_0(sK1,X11) ) ),
    inference(resolution,[],[f168,f237])).

fof(f1072,plain,
    ( m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f1053,f373])).

fof(f373,plain,
    ( ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | m1_subset_1(sK7(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f367,f167])).

fof(f167,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f124])).

fof(f367,plain,
    ( ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | m1_subset_1(sK7(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f326,f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK7(X0,X1),X1)
                & r1_orders_2(X0,sK6(X0,X1),sK7(X0,X1))
                & r2_hidden(sK6(X0,X1),X1)
                & m1_subset_1(sK7(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f132,f134,f133])).

fof(f133,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK6(X0,X1),X3)
            & r2_hidden(sK6(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f134,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,X2,X3)
          & r2_hidden(X2,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r1_orders_2(X0,X2,sK7(X0,X1))
        & r2_hidden(X2,X1)
        & m1_subset_1(sK7(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f132,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',d20_waybel_0)).

fof(f326,plain,
    ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f325,f216])).

fof(f216,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',commutativity_k3_xboole_0)).

fof(f325,plain,
    ( ~ v13_waybel_0(k3_xboole_0(sK2,sK1),sK0)
    | ~ v13_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f324,f172])).

fof(f172,plain,
    ( ~ v13_waybel_0(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ v13_waybel_0(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f124])).

fof(f324,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),sK1,X5) = k3_xboole_0(X5,sK1) ),
    inference(forward_demodulation,[],[f308,f307])).

fof(f307,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK1) = k3_xboole_0(X4,sK1) ),
    inference(resolution,[],[f168,f232])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f57])).

fof(f57,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',redefinition_k9_subset_1)).

fof(f308,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X5) ),
    inference(resolution,[],[f168,f233])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',commutativity_k9_subset_1)).

fof(f1452,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ r2_hidden(sK6(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1445,f1407])).

fof(f1407,plain,
    ( ~ r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f1080,f266])).

fof(f266,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f246])).

fof(f246,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f156])).

fof(f156,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
              & ~ r2_hidden(sK14(X0,X1,X2),X0) )
            | ~ r2_hidden(sK14(X0,X1,X2),X2) )
          & ( r2_hidden(sK14(X0,X1,X2),X1)
            | r2_hidden(sK14(X0,X1,X2),X0)
            | r2_hidden(sK14(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f154,f155])).

fof(f155,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK14(X0,X1,X2),X1)
            & ~ r2_hidden(sK14(X0,X1,X2),X0) )
          | ~ r2_hidden(sK14(X0,X1,X2),X2) )
        & ( r2_hidden(sK14(X0,X1,X2),X1)
          | r2_hidden(sK14(X0,X1,X2),X0)
          | r2_hidden(sK14(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f154,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f153])).

fof(f153,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f152])).

fof(f152,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',d3_xboole_0)).

fof(f1080,plain,
    ( ~ r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f1075,f1053])).

fof(f1075,plain,
    ( ~ r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f1053,f376])).

fof(f376,plain,
    ( ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ r2_hidden(sK7(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f370,f167])).

fof(f370,plain,
    ( ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ r2_hidden(sK7(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f326,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | ~ r2_hidden(sK7(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f1445,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ r2_hidden(sK6(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1079,f327])).

fof(f327,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X1,X0)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f286,f309])).

fof(f309,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK1)
      | m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f168,f234])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f110])).

fof(f110,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f63])).

fof(f63,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',t4_subset)).

fof(f286,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f285,f167])).

fof(f285,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f284,f168])).

fof(f284,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK1)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f170,f192])).

fof(f192,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f170,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f124])).

fof(f1079,plain,
    ( r1_orders_2(sK0,sK6(sK0,k2_xboole_0(sK1,sK2)),sK7(sK0,k2_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f1074,f1053])).

fof(f1074,plain,
    ( r1_orders_2(sK0,sK6(sK0,k2_xboole_0(sK1,sK2)),sK7(sK0,k2_xboole_0(sK1,sK2)))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f1053,f375])).

fof(f375,plain,
    ( ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | r1_orders_2(sK0,sK6(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK7(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f369,f167])).

fof(f369,plain,
    ( ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | r1_orders_2(sK0,sK6(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),sK7(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f326,f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | r1_orders_2(X0,sK6(X0,X1),sK7(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f1451,plain,
    ( ~ r2_hidden(sK6(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1450,f1077])).

fof(f1450,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ r2_hidden(sK6(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1444,f1408])).

fof(f1408,plain,
    ( ~ r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f1080,f265])).

fof(f265,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f247])).

fof(f247,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f156])).

fof(f1444,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | r2_hidden(sK7(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ r2_hidden(sK6(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ m1_subset_1(sK7(sK0,k2_xboole_0(sK1,sK2)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1079,f364])).

fof(f364,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X1,X0)
      | r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f289,f348])).

fof(f348,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,sK2)
      | m1_subset_1(X6,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f169,f234])).

fof(f289,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f288,f167])).

fof(f288,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f287,f169])).

fof(f287,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ r1_orders_2(sK0,X1,X0)
      | ~ r2_hidden(X1,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f171,f192])).

fof(f171,plain,(
    v13_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f124])).

fof(f1392,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | r2_hidden(sK6(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK6(sK0,k2_xboole_0(sK1,sK2)),sK1) ),
    inference(resolution,[],[f1078,f267])).

fof(f267,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f245])).

fof(f245,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f156])).

fof(f1078,plain,
    ( r2_hidden(sK6(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f1073,f1053])).

fof(f1073,plain,
    ( r2_hidden(sK6(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f1053,f374])).

fof(f374,plain,
    ( ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | r2_hidden(sK6(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f368,f167])).

fof(f368,plain,
    ( ~ v13_waybel_0(k3_xboole_0(sK1,sK2),sK0)
    | r2_hidden(sK6(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)),k4_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f326,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(X1,X0)
      | r2_hidden(sK6(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f44225,plain,(
    v13_waybel_0(k3_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f44224,f216])).

fof(f44224,plain,(
    v13_waybel_0(k3_xboole_0(sK2,sK1),sK0) ),
    inference(subsumption_resolution,[],[f44223,f7875])).

fof(f7875,plain,(
    ! [X0] :
      ( v13_waybel_0(k3_xboole_0(X0,sK1),sK0)
      | ~ r2_hidden(sK7(sK0,k3_xboole_0(X0,sK1)),X0) ) ),
    inference(subsumption_resolution,[],[f4679,f7874])).

fof(f7874,plain,(
    ! [X1] :
      ( v13_waybel_0(k3_xboole_0(X1,sK1),sK0)
      | r2_hidden(sK7(sK0,k3_xboole_0(X1,sK1)),sK1) ) ),
    inference(subsumption_resolution,[],[f7873,f617])).

fof(f617,plain,(
    ! [X7] :
      ( v13_waybel_0(k3_xboole_0(X7,sK1),sK0)
      | m1_subset_1(sK7(sK0,k3_xboole_0(X7,sK1)),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f580,f167])).

fof(f580,plain,(
    ! [X7] :
      ( v13_waybel_0(k3_xboole_0(X7,sK1),sK0)
      | m1_subset_1(sK7(sK0,k3_xboole_0(X7,sK1)),u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f323,f194])).

fof(f323,plain,(
    ! [X3] : m1_subset_1(k3_xboole_0(X3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f307,f306])).

fof(f306,plain,(
    ! [X3] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f168,f231])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',dt_k9_subset_1)).

fof(f7873,plain,(
    ! [X1] :
      ( v13_waybel_0(k3_xboole_0(X1,sK1),sK0)
      | r2_hidden(sK7(sK0,k3_xboole_0(X1,sK1)),sK1)
      | ~ m1_subset_1(sK7(sK0,k3_xboole_0(X1,sK1)),u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f7864,f4657])).

fof(f4657,plain,(
    ! [X3] :
      ( v13_waybel_0(k3_xboole_0(X3,sK1),sK0)
      | r2_hidden(sK6(sK0,k3_xboole_0(X3,sK1)),sK1) ) ),
    inference(resolution,[],[f618,f263])).

fof(f263,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f240])).

fof(f240,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f151])).

fof(f151,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
            | ~ r2_hidden(sK13(X0,X1,X2),X0)
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK13(X0,X1,X2),X1)
              & r2_hidden(sK13(X0,X1,X2),X0) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f149,f150])).

fof(f150,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK13(X0,X1,X2),X1)
          | ~ r2_hidden(sK13(X0,X1,X2),X0)
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK13(X0,X1,X2),X1)
            & r2_hidden(sK13(X0,X1,X2),X0) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f149,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f148])).

fof(f148,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f147])).

fof(f147,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t29_waybel_0.p',d4_xboole_0)).

fof(f618,plain,(
    ! [X8] :
      ( r2_hidden(sK6(sK0,k3_xboole_0(X8,sK1)),k3_xboole_0(X8,sK1))
      | v13_waybel_0(k3_xboole_0(X8,sK1),sK0) ) ),
    inference(subsumption_resolution,[],[f581,f167])).

fof(f581,plain,(
    ! [X8] :
      ( v13_waybel_0(k3_xboole_0(X8,sK1),sK0)
      | r2_hidden(sK6(sK0,k3_xboole_0(X8,sK1)),k3_xboole_0(X8,sK1))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f323,f195])).

fof(f7864,plain,(
    ! [X1] :
      ( v13_waybel_0(k3_xboole_0(X1,sK1),sK0)
      | r2_hidden(sK7(sK0,k3_xboole_0(X1,sK1)),sK1)
      | ~ r2_hidden(sK6(sK0,k3_xboole_0(X1,sK1)),sK1)
      | ~ m1_subset_1(sK7(sK0,k3_xboole_0(X1,sK1)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f619,f327])).

fof(f619,plain,(
    ! [X9] :
      ( r1_orders_2(sK0,sK6(sK0,k3_xboole_0(X9,sK1)),sK7(sK0,k3_xboole_0(X9,sK1)))
      | v13_waybel_0(k3_xboole_0(X9,sK1),sK0) ) ),
    inference(subsumption_resolution,[],[f582,f167])).

fof(f582,plain,(
    ! [X9] :
      ( v13_waybel_0(k3_xboole_0(X9,sK1),sK0)
      | r1_orders_2(sK0,sK6(sK0,k3_xboole_0(X9,sK1)),sK7(sK0,k3_xboole_0(X9,sK1)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f323,f196])).

fof(f4679,plain,(
    ! [X0] :
      ( v13_waybel_0(k3_xboole_0(X0,sK1),sK0)
      | ~ r2_hidden(sK7(sK0,k3_xboole_0(X0,sK1)),sK1)
      | ~ r2_hidden(sK7(sK0,k3_xboole_0(X0,sK1)),X0) ) ),
    inference(resolution,[],[f620,f262])).

fof(f262,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f241])).

fof(f241,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f151])).

fof(f620,plain,(
    ! [X10] :
      ( ~ r2_hidden(sK7(sK0,k3_xboole_0(X10,sK1)),k3_xboole_0(X10,sK1))
      | v13_waybel_0(k3_xboole_0(X10,sK1),sK0) ) ),
    inference(subsumption_resolution,[],[f583,f167])).

fof(f583,plain,(
    ! [X10] :
      ( v13_waybel_0(k3_xboole_0(X10,sK1),sK0)
      | ~ r2_hidden(sK7(sK0,k3_xboole_0(X10,sK1)),k3_xboole_0(X10,sK1))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f323,f197])).

fof(f44223,plain,
    ( v13_waybel_0(k3_xboole_0(sK2,sK1),sK0)
    | r2_hidden(sK7(sK0,k3_xboole_0(sK2,sK1)),sK2) ),
    inference(subsumption_resolution,[],[f44152,f675])).

fof(f675,plain,(
    ! [X6] : m1_subset_1(k3_xboole_0(sK2,X6),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f362,f216])).

fof(f362,plain,(
    ! [X3] : m1_subset_1(k3_xboole_0(X3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f346,f345])).

fof(f345,plain,(
    ! [X3] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f169,f231])).

fof(f346,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK2) = k3_xboole_0(X4,sK2) ),
    inference(resolution,[],[f169,f232])).

fof(f44152,plain,
    ( v13_waybel_0(k3_xboole_0(sK2,sK1),sK0)
    | r2_hidden(sK7(sK0,k3_xboole_0(sK2,sK1)),sK2)
    | ~ m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f44113])).

fof(f44113,plain,
    ( v13_waybel_0(k3_xboole_0(sK2,sK1),sK0)
    | r2_hidden(sK7(sK0,k3_xboole_0(sK2,sK1)),sK2)
    | v13_waybel_0(k3_xboole_0(sK2,sK1),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f4656,f1303])).

fof(f1303,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK0,X0),sK2)
      | r2_hidden(sK7(sK0,X0),sK2)
      | v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1302,f274])).

fof(f274,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK7(sK0,X7),u1_struct_0(sK0))
      | v13_waybel_0(X7,sK0) ) ),
    inference(resolution,[],[f167,f194])).

fof(f1302,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,X0),sK2)
      | ~ r2_hidden(sK6(sK0,X0),sK2)
      | ~ m1_subset_1(sK7(sK0,X0),u1_struct_0(sK0))
      | v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1301,f167])).

fof(f1301,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,X0),sK2)
      | ~ r2_hidden(sK6(sK0,X0),sK2)
      | ~ m1_subset_1(sK7(sK0,X0),u1_struct_0(sK0))
      | v13_waybel_0(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f364,f196])).

fof(f4656,plain,(
    ! [X2] :
      ( r2_hidden(sK6(sK0,k3_xboole_0(X2,sK1)),X2)
      | v13_waybel_0(k3_xboole_0(X2,sK1),sK0) ) ),
    inference(resolution,[],[f618,f264])).

fof(f264,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f239])).

fof(f239,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f151])).
%------------------------------------------------------------------------------
