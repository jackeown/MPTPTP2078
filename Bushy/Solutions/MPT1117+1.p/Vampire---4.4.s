%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t48_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:43 EDT 2019

% Result     : Theorem 2.36s
% Output     : Refutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   79 (1297 expanded)
%              Number of leaves         :   12 ( 389 expanded)
%              Depth                    :   27
%              Number of atoms          :  259 (5227 expanded)
%              Number of equality atoms :    6 (  36 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1709,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1708,f1037])).

fof(f1037,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1036,f930])).

fof(f930,plain,(
    ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f928,f64])).

fof(f64,plain,(
    ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k2_pre_topc(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(sK1,k2_pre_topc(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k2_pre_topc(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t48_pre_topc.p',t48_pre_topc)).

fof(f928,plain,(
    k2_pre_topc(sK0,sK1) = k1_xboole_0 ),
    inference(subsumption_resolution,[],[f926,f64])).

fof(f926,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | k2_pre_topc(sK0,sK1) = k1_xboole_0 ),
    inference(resolution,[],[f924,f230])).

fof(f230,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(sK4(X10,X11),X11)
      | r1_tarski(X10,X11)
      | k1_xboole_0 = X11 ) ),
    inference(resolution,[],[f110,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t48_pre_topc.p',t6_boole)).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r1_tarski(X0,X1)
      | ~ m1_subset_1(sK4(X0,X1),X1) ) ),
    inference(resolution,[],[f80,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t48_pre_topc.p',t2_subset)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t48_pre_topc.p',d3_tarski)).

fof(f924,plain,(
    m1_subset_1(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f923,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t48_pre_topc.p',t1_subset)).

fof(f923,plain,
    ( m1_subset_1(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f922,f62])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f922,plain,
    ( m1_subset_1(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f921,f63])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f921,plain,
    ( m1_subset_1(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f920,f117])).

fof(f117,plain,(
    r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f116,f63])).

fof(f116,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
      | r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f114,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t48_pre_topc.p',t3_subset)).

fof(f114,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1,X3)
      | r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),X3) ) ),
    inference(resolution,[],[f78,f93])).

fof(f93,plain,(
    r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(resolution,[],[f79,f64])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f920,plain,
    ( m1_subset_1(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f915])).

fof(f915,plain,
    ( m1_subset_1(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f582,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,sK2(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f49,plain,(
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

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/pre_topc__t48_pre_topc.p',t45_pre_topc)).

fof(f582,plain,(
    ! [X9] :
      ( r2_hidden(sK4(sK1,k2_pre_topc(sK0,sK1)),sK2(sK0,sK1,X9))
      | m1_subset_1(X9,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X9,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f576,f114])).

fof(f576,plain,(
    ! [X3] :
      ( r1_tarski(sK1,sK2(sK0,sK1,X3))
      | ~ r2_hidden(X3,u1_struct_0(sK0))
      | m1_subset_1(X3,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f473,f74])).

fof(f473,plain,(
    ! [X4] :
      ( r2_hidden(X4,k2_pre_topc(sK0,sK1))
      | r1_tarski(sK1,sK2(sK0,sK1,X4))
      | ~ r2_hidden(X4,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f469,f63])).

fof(f469,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,u1_struct_0(sK0))
      | r1_tarski(X0,sK2(sK0,X0,X1))
      | r2_hidden(X1,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f70,f62])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(X1,sK2(X0,X1,X2))
      | ~ r2_hidden(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1036,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f983,f229])).

fof(f229,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(sK4(X7,X8),X8)
      | r1_tarski(X7,X8)
      | ~ r2_hidden(X9,X8) ) ),
    inference(resolution,[],[f110,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t48_pre_topc.p',t7_boole)).

fof(f983,plain,(
    m1_subset_1(sK4(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f928,f924])).

fof(f1708,plain,(
    r2_hidden(sK4(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1707,f928])).

fof(f1707,plain,(
    r2_hidden(sK4(sK1,k1_xboole_0),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1706,f62])).

fof(f1706,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1705,f63])).

fof(f1705,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1699,f940])).

fof(f940,plain,(
    r2_hidden(sK4(sK1,k1_xboole_0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f928,f117])).

fof(f1699,plain,
    ( r2_hidden(sK4(sK1,k1_xboole_0),k2_pre_topc(sK0,sK1))
    | ~ r2_hidden(sK4(sK1,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1696,f71])).

fof(f1696,plain,(
    r2_hidden(sK4(sK1,k1_xboole_0),sK2(sK0,sK1,sK4(sK1,k1_xboole_0))) ),
    inference(resolution,[],[f1603,f940])).

fof(f1603,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(sK4(sK1,k1_xboole_0),sK2(sK0,sK1,X0)) ) ),
    inference(resolution,[],[f986,f937])).

fof(f937,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1,X3)
      | r2_hidden(sK4(sK1,k1_xboole_0),X3) ) ),
    inference(backward_demodulation,[],[f928,f114])).

fof(f986,plain,(
    ! [X4] :
      ( r1_tarski(sK1,sK2(sK0,sK1,X4))
      | ~ r2_hidden(X4,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f473,f929])).

fof(f929,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f927,f64])).

fof(f927,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
      | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) ) ),
    inference(resolution,[],[f924,f229])).
%------------------------------------------------------------------------------
