%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord2__t4_wellord2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:17 EDT 2019

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 168 expanded)
%              Number of leaves         :   12 (  40 expanded)
%              Depth                    :   30
%              Number of atoms          :  405 (1010 expanded)
%              Number of equality atoms :   37 ( 132 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6218,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6214,f72])).

fof(f72,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ~ v6_relat_2(k1_wellord2(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f56])).

fof(f56,plain,
    ( ? [X0] :
        ( ~ v6_relat_2(k1_wellord2(X0))
        & v3_ordinal1(X0) )
   => ( ~ v6_relat_2(k1_wellord2(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ~ v6_relat_2(k1_wellord2(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v6_relat_2(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t4_wellord2.p',t4_wellord2)).

fof(f6214,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f6180,f73])).

fof(f73,plain,(
    ~ v6_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f6180,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f6103,f147])).

fof(f147,plain,(
    ! [X0] :
      ( ~ r6_relat_2(k1_wellord2(X0),X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f145,f75])).

fof(f75,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t4_wellord2.p',dt_k1_wellord2)).

fof(f145,plain,(
    ! [X0] :
      ( ~ r6_relat_2(k1_wellord2(X0),X0)
      | v6_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f78,f119])).

fof(f119,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f116,f75])).

fof(f116,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
              | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
            & r2_hidden(sK5(X0,X1),X0)
            & r2_hidden(sK4(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f67,f68])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X1) )
        & r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t4_wellord2.p',d1_wellord2)).

fof(f78,plain,(
    ! [X0] :
      ( ~ r6_relat_2(X0,k3_relat_1(X0))
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ~ r6_relat_2(X0,k3_relat_1(X0)) )
        & ( r6_relat_2(X0,k3_relat_1(X0))
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> r6_relat_2(X0,k3_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t4_wellord2.p',d14_relat_2)).

fof(f6103,plain,(
    ! [X0] :
      ( r6_relat_2(k1_wellord2(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f6102,f75])).

fof(f6102,plain,(
    ! [X0] :
      ( r6_relat_2(k1_wellord2(X0),X0)
      | ~ v3_ordinal1(X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f6090])).

fof(f6090,plain,(
    ! [X0] :
      ( r6_relat_2(k1_wellord2(X0),X0)
      | ~ v3_ordinal1(X0)
      | r6_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f6067,f263])).

fof(f263,plain,(
    ! [X2,X3] :
      ( v3_ordinal1(sK1(X2,X3))
      | r6_relat_2(X2,X3)
      | ~ v1_relat_1(X2)
      | ~ v3_ordinal1(X3) ) ),
    inference(resolution,[],[f155,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_ordinal1(X1)
          | ~ m1_subset_1(X1,X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t4_wellord2.p',cc5_ordinal1)).

fof(f155,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),X1)
      | ~ v1_relat_1(X0)
      | r6_relat_2(X0,X1) ) ),
    inference(resolution,[],[f80,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t4_wellord2.p',t1_subset)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
              & sK1(X0,X1) != sK2(X0,X1)
              & r2_hidden(sK2(X0,X1),X1)
              & r2_hidden(sK1(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f60,f61])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & X2 != X3
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
        & sK1(X0,X1) != sK2(X0,X1)
        & r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | X4 = X5
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | X2 = X3
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r6_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | X2 = X3
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r6_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & X2 != X3
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t4_wellord2.p',d6_relat_2)).

fof(f6067,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(k1_wellord2(X0),X0))
      | r6_relat_2(k1_wellord2(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f6066,f75])).

fof(f6066,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(k1_wellord2(X0),X0))
      | r6_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f6055])).

fof(f6055,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(k1_wellord2(X0),X0))
      | r6_relat_2(k1_wellord2(X0),X0)
      | r6_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f6049,f277])).

fof(f277,plain,(
    ! [X2,X3] :
      ( v3_ordinal1(sK2(X2,X3))
      | r6_relat_2(X2,X3)
      | ~ v1_relat_1(X2)
      | ~ v3_ordinal1(X3) ) ),
    inference(resolution,[],[f158,f86])).

fof(f158,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),X1)
      | ~ v1_relat_1(X0)
      | r6_relat_2(X0,X1) ) ),
    inference(resolution,[],[f81,f98])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f6049,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK2(k1_wellord2(X0),X0))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X0))
      | r6_relat_2(k1_wellord2(X0),X0) ) ),
    inference(subsumption_resolution,[],[f6048,f75])).

fof(f6048,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK2(k1_wellord2(X0),X0))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X0))
      | r6_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f6038])).

fof(f6038,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK2(k1_wellord2(X0),X0))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X0))
      | r6_relat_2(k1_wellord2(X0),X0)
      | r6_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f1667,f80])).

fof(f1667,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | ~ v3_ordinal1(sK2(k1_wellord2(X0),X0))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X0))
      | r6_relat_2(k1_wellord2(X0),X0) ) ),
    inference(subsumption_resolution,[],[f1666,f75])).

fof(f1666,plain,(
    ! [X0] :
      ( r6_relat_2(k1_wellord2(X0),X0)
      | ~ v3_ordinal1(sK2(k1_wellord2(X0),X0))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X0))
      | ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f1658])).

fof(f1658,plain,(
    ! [X0] :
      ( r6_relat_2(k1_wellord2(X0),X0)
      | ~ v3_ordinal1(sK2(k1_wellord2(X0),X0))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X0))
      | ~ r2_hidden(sK1(k1_wellord2(X0),X0),X0)
      | r6_relat_2(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f747,f81])).

fof(f747,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | r6_relat_2(k1_wellord2(X0),X1)
      | ~ v3_ordinal1(sK2(k1_wellord2(X0),X1))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0) ) ),
    inference(subsumption_resolution,[],[f746,f195])).

fof(f195,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK2(k1_wellord2(X2),X3),sK1(k1_wellord2(X2),X3))
      | ~ r2_hidden(sK1(k1_wellord2(X2),X3),X2)
      | ~ r2_hidden(sK2(k1_wellord2(X2),X3),X2)
      | r6_relat_2(k1_wellord2(X2),X3) ) ),
    inference(subsumption_resolution,[],[f190,f75])).

fof(f190,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(sK2(k1_wellord2(X2),X3),sK1(k1_wellord2(X2),X3))
      | ~ r2_hidden(sK1(k1_wellord2(X2),X3),X2)
      | ~ r2_hidden(sK2(k1_wellord2(X2),X3),X2)
      | r6_relat_2(k1_wellord2(X2),X3)
      | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    inference(resolution,[],[f117,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f117,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f114,f75])).

fof(f114,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f746,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r6_relat_2(k1_wellord2(X0),X1)
      | ~ v3_ordinal1(sK2(k1_wellord2(X0),X1))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | r1_tarski(sK2(k1_wellord2(X0),X1),sK1(k1_wellord2(X0),X1)) ) ),
    inference(duplicate_literal_removal,[],[f744])).

fof(f744,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r6_relat_2(k1_wellord2(X0),X1)
      | ~ v3_ordinal1(sK2(k1_wellord2(X0),X1))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | r1_tarski(sK2(k1_wellord2(X0),X1),sK1(k1_wellord2(X0),X1))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X1))
      | ~ v3_ordinal1(sK2(k1_wellord2(X0),X1)) ) ),
    inference(resolution,[],[f356,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t4_wellord2.p',redefinition_r1_ordinal1)).

fof(f356,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(sK2(k1_wellord2(X0),X1),sK1(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r6_relat_2(k1_wellord2(X0),X1)
      | ~ v3_ordinal1(sK2(k1_wellord2(X0),X1))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK2(k1_wellord2(X0),X1),X0) ) ),
    inference(resolution,[],[f194,f165])).

fof(f165,plain,(
    ! [X2,X1] :
      ( r1_tarski(X1,X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X2,X1) ) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,(
    ! [X2,X1] :
      ( r1_tarski(X1,X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X2,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f102,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord2__t4_wellord2.p',connectedness_r1_ordinal1)).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r6_relat_2(k1_wellord2(X0),X1) ) ),
    inference(subsumption_resolution,[],[f189,f75])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0),X1),sK2(k1_wellord2(X0),X1))
      | ~ r2_hidden(sK2(k1_wellord2(X0),X1),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0),X1),X0)
      | r6_relat_2(k1_wellord2(X0),X1)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f117,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r6_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).
%------------------------------------------------------------------------------
