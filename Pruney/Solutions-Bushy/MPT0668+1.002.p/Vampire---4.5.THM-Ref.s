%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0668+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:25 EST 2020

% Result     : Theorem 8.58s
% Output     : Refutation 9.02s
% Verified   : 
% Statistics : Number of formulae       :  455 (655201822606 expanded)
%              Number of leaves         :    4 (105706093918 expanded)
%              Depth                    :  208
%              Number of atoms          : 1529 (4546821565568 expanded)
%              Number of equality atoms :  740 (1107887655167 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16570,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16566,f16316])).

fof(f16316,plain,(
    r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f16315,f16274])).

fof(f16274,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f16257,f16])).

fof(f16,plain,(
    ! [X4,X2,X0] :
      ( ~ sP5(X4,X2,X0)
      | r2_hidden(k1_funct_1(X2,X4),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <~> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <~> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( k8_relat_1(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
                & ! [X4] :
                    ( r2_hidden(X4,k1_relat_1(X1))
                  <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                      & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( k8_relat_1(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                   => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
                & ! [X3] :
                    ( r2_hidden(X3,k1_relat_1(X1))
                  <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                      & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_1)).

fof(f16257,plain,
    ( sP5(sK3,sK2,sK0)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f16254])).

fof(f16254,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0) ),
    inference(backward_demodulation,[],[f15153,f16212])).

fof(f16212,plain,(
    k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f16205,f71])).

fof(f71,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | k1_funct_1(sK2,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f70,f50])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f70,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | k1_funct_1(sK2,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f67,f24])).

fof(f24,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X2,k1_relat_1(sK2))
      | ~ r2_hidden(k4_tarski(X2,X3),sK2)
      | k1_funct_1(sK2,X2) = X3 ) ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f25,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f16205,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2) ),
    inference(resolution,[],[f16161,f13670])).

fof(f13670,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(k4_tarski(X10,X11),sK1)
      | r2_hidden(k4_tarski(X10,X11),sK2) ) ),
    inference(subsumption_resolution,[],[f13669,f26])).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f13669,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(k4_tarski(X10,X11),sK1)
      | ~ v1_relat_1(sK1)
      | r2_hidden(k4_tarski(X10,X11),sK2) ) ),
    inference(subsumption_resolution,[],[f13664,f24])).

fof(f13664,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(k4_tarski(X10,X11),sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | r2_hidden(k4_tarski(X10,X11),sK2) ) ),
    inference(superposition,[],[f47,f13641])).

fof(f13641,plain,(
    sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f13640,f13481])).

fof(f13481,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f13475])).

fof(f13475,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f13474,f12385])).

fof(f12385,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f12384,f12382])).

fof(f12382,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f12348])).

fof(f12348,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f6715,f12345])).

fof(f12345,plain,
    ( k1_xboole_0 = sK7(sK0,sK2,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f12344,f12236])).

fof(f12236,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1)
    | k1_xboole_0 = sK7(sK0,sK2,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f170,f12228])).

fof(f12228,plain,
    ( sK7(sK0,sK2,sK1) = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f12160])).

fof(f12160,plain,
    ( sK7(sK0,sK2,sK1) = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2)
    | sK7(sK0,sK2,sK1) = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2)
    | sK7(sK0,sK2,sK1) = k1_funct_1(sK1,sK6(sK0,sK2,sK1)) ),
    inference(superposition,[],[f11189,f8097])).

fof(f8097,plain,(
    ! [X2] :
      ( sK7(X2,sK2,sK1) = k1_funct_1(sK2,sK6(X2,sK2,sK1))
      | sK1 = k8_relat_1(X2,sK2)
      | sK7(X2,sK2,sK1) = k1_funct_1(sK1,sK6(X2,sK2,sK1)) ) ),
    inference(resolution,[],[f1854,f93])).

fof(f93,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f92,f50])).

fof(f92,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3 ) ),
    inference(subsumption_resolution,[],[f89,f26])).

fof(f89,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X2,k1_relat_1(sK1))
      | ~ r2_hidden(k4_tarski(X2,X3),sK1)
      | k1_funct_1(sK1,X2) = X3 ) ),
    inference(resolution,[],[f27,f30])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f1854,plain,(
    ! [X4] :
      ( r2_hidden(k4_tarski(sK6(X4,sK2,sK1),sK7(X4,sK2,sK1)),sK1)
      | k1_funct_1(sK2,sK6(X4,sK2,sK1)) = sK7(X4,sK2,sK1)
      | sK1 = k8_relat_1(X4,sK2) ) ),
    inference(resolution,[],[f131,f26])).

fof(f131,plain,(
    ! [X6,X5] :
      ( ~ v1_relat_1(X6)
      | k1_funct_1(sK2,sK6(X5,sK2,X6)) = sK7(X5,sK2,X6)
      | r2_hidden(k4_tarski(sK6(X5,sK2,X6),sK7(X5,sK2,X6)),X6)
      | k8_relat_1(X5,sK2) = X6 ) ),
    inference(subsumption_resolution,[],[f126,f24])).

fof(f126,plain,(
    ! [X6,X5] :
      ( k1_funct_1(sK2,sK6(X5,sK2,X6)) = sK7(X5,sK2,X6)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X6)
      | r2_hidden(k4_tarski(sK6(X5,sK2,X6),sK7(X5,sK2,X6)),X6)
      | k8_relat_1(X5,sK2) = X6 ) ),
    inference(resolution,[],[f71,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

fof(f11189,plain,
    ( k1_funct_1(sK2,sK6(sK0,sK2,sK1)) = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2)
    | sK7(sK0,sK2,sK1) = k1_funct_1(sK1,sK6(sK0,sK2,sK1)) ),
    inference(duplicate_literal_removal,[],[f11162])).

fof(f11162,plain,
    ( sK7(sK0,sK2,sK1) = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2)
    | k1_funct_1(sK2,sK6(sK0,sK2,sK1)) = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f11160,f17])).

fof(f17,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK1))
      | k1_funct_1(sK2,X3) = k1_funct_1(sK1,X3)
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f11160,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1))
    | sK7(sK0,sK2,sK1) = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f11157])).

fof(f11157,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | sK7(sK0,sK2,sK1) = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f11149,f22])).

fof(f22,plain,(
    ! [X4] :
      ( ~ sP5(X4,sK2,sK0)
      | r2_hidden(X4,k1_relat_1(sK1))
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f11149,plain,(
    ! [X1] :
      ( sP5(sK6(X1,sK2,sK1),sK2,X1)
      | sK1 = k8_relat_1(X1,sK2)
      | sK7(X1,sK2,sK1) = k1_funct_1(sK1,sK6(X1,sK2,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f11110])).

fof(f11110,plain,(
    ! [X1] :
      ( sP5(sK6(X1,sK2,sK1),sK2,X1)
      | sK1 = k8_relat_1(X1,sK2)
      | sK7(X1,sK2,sK1) = k1_funct_1(sK1,sK6(X1,sK2,sK1))
      | sK7(X1,sK2,sK1) = k1_funct_1(sK1,sK6(X1,sK2,sK1))
      | sK1 = k8_relat_1(X1,sK2) ) ),
    inference(resolution,[],[f8468,f1622])).

fof(f1622,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3,sK2,sK1),X3)
      | k1_funct_1(sK1,sK6(X3,sK2,sK1)) = sK7(X3,sK2,sK1)
      | sK1 = k8_relat_1(X3,sK2) ) ),
    inference(resolution,[],[f152,f24])).

fof(f152,plain,(
    ! [X8,X7] :
      ( ~ v1_relat_1(X8)
      | k1_funct_1(sK1,sK6(X7,X8,sK1)) = sK7(X7,X8,sK1)
      | r2_hidden(sK7(X7,X8,sK1),X7)
      | sK1 = k8_relat_1(X7,X8) ) ),
    inference(subsumption_resolution,[],[f147,f26])).

fof(f147,plain,(
    ! [X8,X7] :
      ( k1_funct_1(sK1,sK6(X7,X8,sK1)) = sK7(X7,X8,sK1)
      | ~ v1_relat_1(X8)
      | ~ v1_relat_1(sK1)
      | r2_hidden(sK7(X7,X8,sK1),X7)
      | sK1 = k8_relat_1(X7,X8) ) ),
    inference(resolution,[],[f93,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8468,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(sK7(X17,sK2,sK1),X18)
      | sP5(sK6(X17,sK2,sK1),sK2,X18)
      | sK1 = k8_relat_1(X17,sK2)
      | k1_funct_1(sK1,sK6(X17,sK2,sK1)) = sK7(X17,sK2,sK1) ) ),
    inference(subsumption_resolution,[],[f8460,f8334])).

fof(f8334,plain,(
    ! [X2] :
      ( r2_hidden(sK6(X2,sK2,sK1),k1_relat_1(sK2))
      | sK1 = k8_relat_1(X2,sK2)
      | sK7(X2,sK2,sK1) = k1_funct_1(sK1,sK6(X2,sK2,sK1)) ) ),
    inference(resolution,[],[f2251,f50])).

fof(f2251,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK6(X3,sK2,sK1),sK7(X3,sK2,sK1)),sK2)
      | k1_funct_1(sK1,sK6(X3,sK2,sK1)) = sK7(X3,sK2,sK1)
      | sK1 = k8_relat_1(X3,sK2) ) ),
    inference(resolution,[],[f153,f24])).

fof(f153,plain,(
    ! [X10,X9] :
      ( ~ v1_relat_1(X10)
      | k1_funct_1(sK1,sK6(X9,X10,sK1)) = sK7(X9,X10,sK1)
      | r2_hidden(k4_tarski(sK6(X9,X10,sK1),sK7(X9,X10,sK1)),X10)
      | sK1 = k8_relat_1(X9,X10) ) ),
    inference(subsumption_resolution,[],[f148,f26])).

fof(f148,plain,(
    ! [X10,X9] :
      ( k1_funct_1(sK1,sK6(X9,X10,sK1)) = sK7(X9,X10,sK1)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(sK1)
      | r2_hidden(k4_tarski(sK6(X9,X10,sK1),sK7(X9,X10,sK1)),X10)
      | sK1 = k8_relat_1(X9,X10) ) ),
    inference(resolution,[],[f93,f35])).

fof(f8460,plain,(
    ! [X17,X18] :
      ( ~ r2_hidden(sK7(X17,sK2,sK1),X18)
      | ~ r2_hidden(sK6(X17,sK2,sK1),k1_relat_1(sK2))
      | sP5(sK6(X17,sK2,sK1),sK2,X18)
      | sK1 = k8_relat_1(X17,sK2)
      | k1_funct_1(sK1,sK6(X17,sK2,sK1)) = sK7(X17,sK2,sK1) ) ),
    inference(superposition,[],[f14,f8097])).

fof(f14,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
      | ~ r2_hidden(X4,k1_relat_1(X2))
      | sP5(X4,X2,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f170,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK1)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f94,f91])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f87,f26])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(X0,k1_relat_1(sK1))
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f27,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_xboole_0 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 != X2
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f94,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1) ) ),
    inference(subsumption_resolution,[],[f90,f26])).

fof(f90,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X4,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK1,X4)),sK1) ) ),
    inference(resolution,[],[f27,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f12344,plain,
    ( k1_xboole_0 = sK7(sK0,sK2,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f12343,f6497])).

fof(f6497,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK1)
      | r2_hidden(X12,sK0) ) ),
    inference(subsumption_resolution,[],[f6494,f26])).

fof(f6494,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK1)
      | ~ v1_relat_1(sK1)
      | r2_hidden(X12,sK0) ) ),
    inference(duplicate_literal_removal,[],[f6493])).

fof(f6493,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK1)
      | r2_hidden(X12,sK0) ) ),
    inference(superposition,[],[f48,f6480])).

fof(f6480,plain,(
    sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f6479,f4321])).

fof(f4321,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f4320,f2706])).

fof(f2706,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | k1_xboole_0 = k1_funct_1(sK1,X0)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(resolution,[],[f2603,f71])).

fof(f2603,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK2)
      | sK1 = k8_relat_1(sK0,sK1)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f2536,f170])).

fof(f2536,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),sK1)
      | r2_hidden(k4_tarski(X8,X9),sK2)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f2535,f26])).

fof(f2535,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),sK1)
      | ~ v1_relat_1(sK1)
      | r2_hidden(k4_tarski(X8,X9),sK2)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f2529,f24])).

fof(f2529,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | r2_hidden(k4_tarski(X8,X9),sK2)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(superposition,[],[f47,f2517])).

fof(f2517,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2514,f2357])).

fof(f2357,plain,
    ( ~ r2_hidden(k1_xboole_0,sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f2354])).

fof(f2354,plain,
    ( ~ r2_hidden(k1_xboole_0,sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f2242,f2244])).

fof(f2244,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f2237,f26])).

fof(f2237,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f2234])).

fof(f2234,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK6(sK0,sK1,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f35,f2224])).

fof(f2224,plain,
    ( k1_xboole_0 = sK7(sK0,sK1,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f2221])).

fof(f2221,plain,
    ( k1_xboole_0 = sK7(sK0,sK1,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = sK7(sK0,sK1,sK1) ),
    inference(resolution,[],[f2162,f2179])).

fof(f2179,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK7(X0,sK1,sK1),X0)
      | sK1 = k8_relat_1(X0,sK1)
      | k1_xboole_0 = sK7(X0,sK1,sK1) ) ),
    inference(subsumption_resolution,[],[f2178,f2163])).

fof(f2163,plain,(
    ! [X4] :
      ( r2_hidden(k4_tarski(sK6(X4,sK1,sK1),sK7(X4,sK1,sK1)),sK1)
      | k1_xboole_0 = sK7(X4,sK1,sK1)
      | sK1 = k8_relat_1(X4,sK1) ) ),
    inference(superposition,[],[f170,f2156])).

fof(f2156,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,sK6(X4,sK1,sK1)) = sK7(X4,sK1,sK1)
      | sK1 = k8_relat_1(X4,sK1) ) ),
    inference(subsumption_resolution,[],[f2155,f93])).

fof(f2155,plain,(
    ! [X4] :
      ( k1_funct_1(sK1,sK6(X4,sK1,sK1)) = sK7(X4,sK1,sK1)
      | r2_hidden(k4_tarski(sK6(X4,sK1,sK1),sK7(X4,sK1,sK1)),sK1)
      | sK1 = k8_relat_1(X4,sK1) ) ),
    inference(resolution,[],[f151,f26])).

fof(f151,plain,(
    ! [X6,X5] :
      ( ~ v1_relat_1(X6)
      | k1_funct_1(sK1,sK6(X5,sK1,X6)) = sK7(X5,sK1,X6)
      | r2_hidden(k4_tarski(sK6(X5,sK1,X6),sK7(X5,sK1,X6)),X6)
      | k8_relat_1(X5,sK1) = X6 ) ),
    inference(subsumption_resolution,[],[f146,f26])).

fof(f146,plain,(
    ! [X6,X5] :
      ( k1_funct_1(sK1,sK6(X5,sK1,X6)) = sK7(X5,sK1,X6)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X6)
      | r2_hidden(k4_tarski(sK6(X5,sK1,X6),sK7(X5,sK1,X6)),X6)
      | k8_relat_1(X5,sK1) = X6 ) ),
    inference(resolution,[],[f93,f35])).

fof(f2178,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK7(X0,sK1,sK1)
      | sK1 = k8_relat_1(X0,sK1)
      | ~ r2_hidden(sK7(X0,sK1,sK1),X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,sK1,sK1),sK7(X0,sK1,sK1)),sK1) ) ),
    inference(subsumption_resolution,[],[f2177,f26])).

fof(f2177,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK7(X0,sK1,sK1)
      | sK1 = k8_relat_1(X0,sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(sK7(X0,sK1,sK1),X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,sK1,sK1),sK7(X0,sK1,sK1)),sK1) ) ),
    inference(duplicate_literal_removal,[],[f2169])).

fof(f2169,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK7(X0,sK1,sK1)
      | sK1 = k8_relat_1(X0,sK1)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(sK7(X0,sK1,sK1),X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,sK1,sK1),sK7(X0,sK1,sK1)),sK1)
      | sK1 = k8_relat_1(X0,sK1) ) ),
    inference(resolution,[],[f2163,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(sK7(X0,X1,X2),X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X1)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | k8_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2162,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3,sK1,sK1),sK0)
      | k1_xboole_0 = sK7(X3,sK1,sK1)
      | sK1 = k8_relat_1(sK0,sK2)
      | sK1 = k8_relat_1(X3,sK1) ) ),
    inference(superposition,[],[f454,f2156])).

fof(f454,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),sK0)
      | k1_xboole_0 = k1_funct_1(sK1,X0)
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,X0),sK0)
      | k1_xboole_0 = k1_funct_1(sK1,X0)
      | sK1 = k8_relat_1(sK0,sK2)
      | sK1 = k8_relat_1(sK0,sK2)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(superposition,[],[f289,f309])).

fof(f309,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | sK1 = k8_relat_1(sK0,sK2)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f17,f91])).

fof(f289,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),sK0)
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(resolution,[],[f272,f16])).

fof(f272,plain,(
    ! [X0] :
      ( sP5(X0,sK2,sK0)
      | sK1 = k8_relat_1(sK0,sK2)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f23,f91])).

fof(f23,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK1))
      | sP5(X4,sK2,sK0)
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f2242,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK1,sK1),k1_xboole_0),sK1)
    | ~ r2_hidden(k1_xboole_0,sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f2240,f26])).

fof(f2240,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK1,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(k1_xboole_0,sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f2230])).

fof(f2230,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK1,sK1),k1_xboole_0),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(k1_xboole_0,sK0)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK1,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f33,f2224])).

fof(f2514,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f2508])).

fof(f2508,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f2503,f2245])).

fof(f2245,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK6(sK0,sK1,sK1))
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f2244,f93])).

fof(f2503,plain,
    ( r2_hidden(k1_funct_1(sK1,sK6(sK0,sK1,sK1)),sK0)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f2484])).

fof(f2484,plain,
    ( r2_hidden(k1_funct_1(sK1,sK6(sK0,sK1,sK1)),sK0)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f2276,f2274])).

fof(f2274,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1,sK1)) = k1_funct_1(sK2,sK6(sK0,sK1,sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f2253])).

fof(f2253,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_funct_1(sK1,sK6(sK0,sK1,sK1)) = k1_funct_1(sK2,sK6(sK0,sK1,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f2246,f17])).

fof(f2246,plain,
    ( r2_hidden(sK6(sK0,sK1,sK1),k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f2244,f50])).

fof(f2276,plain,
    ( r2_hidden(k1_funct_1(sK2,sK6(sK0,sK1,sK1)),sK0)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f2273,f16])).

fof(f2273,plain,
    ( sP5(sK6(sK0,sK1,sK1),sK2,sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f2254])).

fof(f2254,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | sP5(sK6(sK0,sK1,sK1),sK2,sK0)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f2246,f23])).

fof(f4320,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4) ),
    inference(subsumption_resolution,[],[f4319,f2517])).

fof(f4319,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f4314,f4036])).

fof(f4036,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(subsumption_resolution,[],[f4035,f3361])).

fof(f3361,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f2855,f16])).

fof(f2855,plain,
    ( sP5(sK3,sK2,sK0)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2841,f2517])).

fof(f2841,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0)
    | sK1 != k8_relat_1(sK0,sK2)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f2822])).

fof(f2822,plain,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0)
    | sK1 != k8_relat_1(sK0,sK2)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f21,f2706])).

fof(f21,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0)
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f4035,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f4034,f50])).

fof(f4034,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK1) ),
    inference(duplicate_literal_removal,[],[f4022])).

fof(f4022,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f3365,f2534])).

fof(f2534,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),sK2)
      | ~ r2_hidden(X5,sK0)
      | r2_hidden(k4_tarski(X4,X5),sK1)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f2533,f26])).

fof(f2533,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(k4_tarski(X4,X5),sK2)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f2527,f24])).

fof(f2527,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(X4,X5),sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X5,sK0)
      | ~ r2_hidden(k4_tarski(X4,X5),sK2)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(superposition,[],[f46,f2517])).

fof(f46,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3365,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f3362,f72])).

fof(f72,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK2))
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) ) ),
    inference(subsumption_resolution,[],[f68,f24])).

fof(f68,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(X4,k1_relat_1(sK2))
      | r2_hidden(k4_tarski(X4,k1_funct_1(sK2,X4)),sK2) ) ),
    inference(resolution,[],[f25,f43])).

fof(f3362,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f2855,f15])).

fof(f15,plain,(
    ! [X4,X2,X0] :
      ( ~ sP5(X4,X2,X0)
      | r2_hidden(X4,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4314,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f4313,f19])).

fof(f19,plain,
    ( ~ sP5(sK3,sK2,sK0)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f4313,plain,
    ( sP5(sK3,sK2,sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(subsumption_resolution,[],[f4303,f4168])).

fof(f4168,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f4165,f50])).

fof(f4165,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(duplicate_literal_removal,[],[f4157])).

fof(f4157,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(k4_tarski(sK3,k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f4154,f2536])).

fof(f4154,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f4150])).

fof(f4150,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f4045,f3147])).

fof(f3147,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f3144,f3034])).

fof(f3034,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK4)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f3033])).

fof(f3033,plain,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(duplicate_literal_removal,[],[f3027])).

fof(f3027,plain,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f2967,f2706])).

fof(f2967,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f2966,f91])).

fof(f2966,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4) ),
    inference(subsumption_resolution,[],[f2964,f2517])).

fof(f2964,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f2960,f19])).

fof(f2960,plain,(
    ! [X0] :
      ( sP5(X0,sK2,sK0)
      | k1_xboole_0 = k1_funct_1(sK1,X0)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f2940,f2707])).

fof(f2707,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_relat_1(sK2))
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(resolution,[],[f2603,f50])).

fof(f2940,plain,(
    ! [X0] :
      ( sK1 = k8_relat_1(sK0,sK1)
      | k1_xboole_0 = k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | sP5(X0,sK2,sK0) ) ),
    inference(resolution,[],[f2935,f14])).

fof(f2935,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),sK0)
      | sK1 = k8_relat_1(sK0,sK1)
      | k1_xboole_0 = k1_funct_1(sK1,X1) ) ),
    inference(duplicate_literal_removal,[],[f2928])).

fof(f2928,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),sK0)
      | sK1 = k8_relat_1(sK0,sK1)
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(superposition,[],[f2573,f2788])).

fof(f2788,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = sK9(sK1,X0)
      | k1_xboole_0 = k1_funct_1(sK1,X0)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(resolution,[],[f2651,f71])).

fof(f2651,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK9(sK1,X0)),sK2)
      | sK1 = k8_relat_1(sK0,sK1)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f2605,f91])).

fof(f2605,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | sK1 = k8_relat_1(sK0,sK1)
      | r2_hidden(k4_tarski(X2,sK9(sK1,X2)),sK2) ) ),
    inference(resolution,[],[f2536,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK9(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK9(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2573,plain,(
    ! [X0] :
      ( r2_hidden(sK9(sK1,X0),sK0)
      | sK1 = k8_relat_1(sK0,sK1)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f2553,f91])).

fof(f2553,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | sK1 = k8_relat_1(sK0,sK1)
      | r2_hidden(sK9(sK1,X2),sK0) ) ),
    inference(resolution,[],[f2538,f49])).

fof(f2538,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK1)
      | r2_hidden(X12,sK0)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f2537,f26])).

fof(f2537,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK1)
      | ~ v1_relat_1(sK1)
      | r2_hidden(X12,sK0)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f2531,f24])).

fof(f2531,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | r2_hidden(X12,sK0)
      | sK1 = k8_relat_1(sK0,sK1) ) ),
    inference(superposition,[],[f48,f2517])).

fof(f3144,plain,
    ( k1_xboole_0 != k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f3122])).

fof(f3122,plain,
    ( k1_xboole_0 != k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f2967,f3098])).

fof(f3098,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f3097,f71])).

fof(f3097,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f3089])).

fof(f3089,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f3086,f2536])).

fof(f3086,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f3082])).

fof(f3082,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f2975,f3034])).

fof(f2975,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f2969,f94])).

fof(f2969,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f2968,f91])).

fof(f2968,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f2965,f2517])).

fof(f2965,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f2960,f18])).

fof(f18,plain,
    ( ~ sP5(sK3,sK2,sK0)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f4045,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f4036,f94])).

fof(f4303,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | sP5(sK3,sK2,sK0) ),
    inference(resolution,[],[f4298,f14])).

fof(f4298,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f4289])).

fof(f4289,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(superposition,[],[f4062,f4224])).

fof(f4224,plain,
    ( k1_funct_1(sK2,sK3) = sK9(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f4063,f71])).

fof(f4063,plain,
    ( r2_hidden(k4_tarski(sK3,sK9(sK1,sK3)),sK2)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f4040])).

fof(f4040,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(k4_tarski(sK3,sK9(sK1,sK3)),sK2) ),
    inference(resolution,[],[f4036,f2605])).

fof(f4062,plain,
    ( r2_hidden(sK9(sK1,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f4041])).

fof(f4041,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK9(sK1,sK3),sK0) ),
    inference(resolution,[],[f4036,f2553])).

fof(f6479,plain,
    ( k1_xboole_0 != k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f6464])).

fof(f6464,plain,
    ( k1_xboole_0 != k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f6231,f5740])).

fof(f5740,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f5739,f71])).

fof(f5739,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2) ),
    inference(duplicate_literal_removal,[],[f5731])).

fof(f5731,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f5728,f2536])).

fof(f5728,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f5722])).

fof(f5722,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f5502,f4321])).

fof(f5502,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f5491,f94])).

fof(f5491,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f5490,f2517])).

fof(f5490,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f5483,f5191])).

fof(f5191,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f5190,f71])).

fof(f5190,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2) ),
    inference(duplicate_literal_removal,[],[f5182])).

fof(f5182,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f5179,f2536])).

fof(f5179,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f5173])).

fof(f5173,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f5086,f4321])).

fof(f5086,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f5073,f94])).

fof(f5073,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f5058])).

fof(f5058,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK4,k1_relat_1(sK1)) ),
    inference(resolution,[],[f5055,f2702])).

fof(f2702,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK4,k1_relat_1(sK1)) ),
    inference(resolution,[],[f2532,f16])).

fof(f2532,plain,
    ( sP5(sK3,sK2,sK0)
    | r2_hidden(sK4,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f2521])).

fof(f2521,plain,
    ( sK1 != sK1
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f20,f2517])).

fof(f20,plain,
    ( sK1 != k8_relat_1(sK0,sK2)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f5055,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f5054,f50])).

fof(f5054,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK1) ),
    inference(duplicate_literal_removal,[],[f5038])).

fof(f5038,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f4546,f2534])).

fof(f4546,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f4522,f72])).

fof(f4522,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(resolution,[],[f4339,f71])).

fof(f4339,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2)
    | r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f4328])).

fof(f4328,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2)
    | r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f3559,f4321])).

fof(f3559,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2)
    | r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f3546])).

fof(f3546,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f2771,f2536])).

fof(f2771,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f2703,f94])).

fof(f2703,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f2532,f15])).

fof(f5483,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f5481,f18])).

fof(f5481,plain,
    ( sP5(sK3,sK2,sK0)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f5467,f5331])).

fof(f5331,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(resolution,[],[f5328,f50])).

fof(f5328,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK2)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f5320])).

fof(f5320,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(k4_tarski(sK3,k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f5317,f2536])).

fof(f5317,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f5313])).

fof(f5313,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f5201,f3147])).

fof(f5201,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(resolution,[],[f5191,f94])).

fof(f5467,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | sP5(sK3,sK2,sK0) ),
    inference(resolution,[],[f5452,f14])).

fof(f5452,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f5441])).

fof(f5441,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f5218,f5401])).

fof(f5401,plain,
    ( k1_funct_1(sK2,sK3) = sK9(sK1,sK3)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f5219,f71])).

fof(f5219,plain,
    ( r2_hidden(k4_tarski(sK3,sK9(sK1,sK3)),sK2)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f5196])).

fof(f5196,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(k4_tarski(sK3,sK9(sK1,sK3)),sK2) ),
    inference(resolution,[],[f5191,f2605])).

fof(f5218,plain,
    ( r2_hidden(sK9(sK1,sK3),sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f5197])).

fof(f5197,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK9(sK1,sK3),sK0) ),
    inference(resolution,[],[f5191,f2553])).

fof(f6231,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f6230,f2517])).

fof(f6230,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f6225,f5917])).

fof(f5917,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f5916,f5778])).

fof(f5778,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f5774,f16])).

fof(f5774,plain,
    ( sP5(sK3,sK2,sK0)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f5773,f2517])).

fof(f5773,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0)
    | sK1 != k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f5744,f4321])).

fof(f5744,plain,
    ( k1_xboole_0 != k1_funct_1(sK1,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0)
    | sK1 != k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f21,f5740])).

fof(f5916,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f5915,f50])).

fof(f5915,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK1) ),
    inference(duplicate_literal_removal,[],[f5899])).

fof(f5899,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f5782,f2534])).

fof(f5782,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK2)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f5779,f72])).

fof(f5779,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f5774,f15])).

fof(f6225,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | sK1 != k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f6224,f19])).

fof(f6224,plain,
    ( sP5(sK3,sK2,sK0)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f6208,f6042])).

fof(f6042,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f6039,f50])).

fof(f6039,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f6031])).

fof(f6031,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(k4_tarski(sK3,k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f6028,f2536])).

fof(f6028,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f6024])).

fof(f6024,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f5927,f3147])).

fof(f5927,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f5917,f94])).

fof(f6208,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | sP5(sK3,sK2,sK0) ),
    inference(resolution,[],[f6188,f14])).

fof(f6188,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f6177])).

fof(f6177,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(superposition,[],[f5944,f6128])).

fof(f6128,plain,
    ( k1_funct_1(sK2,sK3) = sK9(sK1,sK3)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f5945,f71])).

fof(f5945,plain,
    ( r2_hidden(k4_tarski(sK3,sK9(sK1,sK3)),sK2)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f5922])).

fof(f5922,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(k4_tarski(sK3,sK9(sK1,sK3)),sK2) ),
    inference(resolution,[],[f5917,f2605])).

fof(f5944,plain,
    ( r2_hidden(sK9(sK1,sK3),sK0)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f5923])).

fof(f5923,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | sK1 = k8_relat_1(sK0,sK1)
    | r2_hidden(sK9(sK1,sK3),sK0) ),
    inference(resolution,[],[f5917,f2553])).

fof(f48,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f12343,plain,
    ( k1_xboole_0 = sK7(sK0,sK2,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | ~ r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f12342,f26])).

fof(f12342,plain,
    ( k1_xboole_0 = sK7(sK0,sK2,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f12341,f24])).

fof(f12341,plain,
    ( k1_xboole_0 = sK7(sK0,sK2,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1) ),
    inference(duplicate_literal_removal,[],[f12335])).

fof(f12335,plain,
    ( k1_xboole_0 = sK7(sK0,sK2,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f12248,f33])).

fof(f12248,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK2)
    | k1_xboole_0 = sK7(sK0,sK2,sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f12237])).

fof(f12237,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),sK7(sK0,sK2,sK1)),sK2)
    | k1_xboole_0 = sK7(sK0,sK2,sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f453,f12228])).

fof(f453,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK2)
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(duplicate_literal_removal,[],[f447])).

fof(f447,plain,(
    ! [X1] :
      ( r2_hidden(k4_tarski(X1,k1_funct_1(sK1,X1)),sK2)
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | sK1 = k8_relat_1(sK0,sK2)
      | k1_xboole_0 = k1_funct_1(sK1,X1) ) ),
    inference(superposition,[],[f154,f309])).

fof(f154,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK2,X0)),sK2)
      | k1_xboole_0 = k1_funct_1(sK2,X0) ) ),
    inference(resolution,[],[f72,f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK2))
      | k1_xboole_0 = k1_funct_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f65,f24])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | r2_hidden(X0,k1_relat_1(sK2))
      | k1_xboole_0 = k1_funct_1(sK2,X0) ) ),
    inference(resolution,[],[f25,f45])).

fof(f6715,plain,
    ( r2_hidden(sK7(sK0,sK2,sK1),sK0)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(factoring,[],[f6682])).

fof(f6682,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3,sK2,sK1),sK0)
      | r2_hidden(sK7(X3,sK2,sK1),X3)
      | sK1 = k8_relat_1(X3,sK2) ) ),
    inference(resolution,[],[f6512,f24])).

fof(f6512,plain,(
    ! [X12,X11] :
      ( ~ v1_relat_1(X12)
      | r2_hidden(sK7(X11,X12,sK1),sK0)
      | r2_hidden(sK7(X11,X12,sK1),X11)
      | sK1 = k8_relat_1(X11,X12) ) ),
    inference(subsumption_resolution,[],[f6505,f26])).

fof(f6505,plain,(
    ! [X12,X11] :
      ( r2_hidden(sK7(X11,X12,sK1),sK0)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(sK1)
      | r2_hidden(sK7(X11,X12,sK1),X11)
      | sK1 = k8_relat_1(X11,X12) ) ),
    inference(resolution,[],[f6497,f34])).

fof(f12384,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | ~ r2_hidden(k1_xboole_0,sK0)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f12383,f26])).

fof(f12383,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(k1_xboole_0,sK0)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f12370,f24])).

fof(f12370,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(k1_xboole_0,sK0)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f12360])).

fof(f12360,plain,
    ( ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(k1_xboole_0,sK0)
    | ~ r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f33,f12345])).

fof(f13474,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f13460])).

fof(f13460,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f13350,f13195])).

fof(f13195,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f13159,f12372])).

fof(f12372,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f12371])).

fof(f12371,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = k8_relat_1(sK0,sK2)
    | k1_xboole_0 = k1_funct_1(sK1,sK6(sK0,sK2,sK1)) ),
    inference(duplicate_literal_removal,[],[f12358])).

fof(f12358,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK2)
    | k1_xboole_0 = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f11102,f12345])).

fof(f11102,plain,(
    ! [X0] :
      ( k1_xboole_0 != sK7(X0,sK2,sK1)
      | sK1 = k8_relat_1(X0,sK2)
      | sK1 = k8_relat_1(sK0,sK2)
      | k1_xboole_0 = k1_funct_1(sK1,sK6(X0,sK2,sK1)) ) ),
    inference(equality_factoring,[],[f8467])).

fof(f8467,plain,(
    ! [X1] :
      ( sK7(X1,sK2,sK1) = k1_funct_1(sK1,sK6(X1,sK2,sK1))
      | sK1 = k8_relat_1(X1,sK2)
      | sK1 = k8_relat_1(sK0,sK2)
      | k1_xboole_0 = k1_funct_1(sK1,sK6(X1,sK2,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f8442])).

fof(f8442,plain,(
    ! [X1] :
      ( sK7(X1,sK2,sK1) = k1_funct_1(sK1,sK6(X1,sK2,sK1))
      | sK1 = k8_relat_1(X1,sK2)
      | sK7(X1,sK2,sK1) = k1_funct_1(sK1,sK6(X1,sK2,sK1))
      | sK1 = k8_relat_1(sK0,sK2)
      | k1_xboole_0 = k1_funct_1(sK1,sK6(X1,sK2,sK1)) ) ),
    inference(superposition,[],[f8097,f309])).

fof(f13159,plain,
    ( k1_xboole_0 != k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(equality_factoring,[],[f12461])).

fof(f12461,plain,
    ( k1_funct_1(sK2,sK6(sK0,sK2,sK1)) = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f12434])).

fof(f12434,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | k1_xboole_0 = k1_funct_1(sK2,sK6(sK0,sK2,sK1))
    | k1_funct_1(sK2,sK6(sK0,sK2,sK1)) = k1_funct_1(sK1,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f12429,f17])).

fof(f12429,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK2)
    | k1_xboole_0 = k1_funct_1(sK2,sK6(sK0,sK2,sK1)) ),
    inference(resolution,[],[f12380,f50])).

fof(f12380,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f12350])).

fof(f12350,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK6(sK0,sK2,sK1))
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f1854,f12345])).

fof(f13350,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_funct_1(sK2,sK6(sK0,sK2,sK1))),sK2)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f13346,f72])).

fof(f13346,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f13341,f15])).

fof(f13341,plain,
    ( sP5(sK6(sK0,sK2,sK1),sK2,sK0)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f13340,f23])).

fof(f13340,plain,
    ( sP5(sK6(sK0,sK2,sK1),sK2,sK0)
    | sK1 = k8_relat_1(sK0,sK2)
    | r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f13322])).

fof(f13322,plain,
    ( sP5(sK6(sK0,sK2,sK1),sK2,sK0)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK2)
    | r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1)) ),
    inference(resolution,[],[f13321,f12479])).

fof(f12479,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2))
    | sK1 = k8_relat_1(sK0,sK2)
    | r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1)) ),
    inference(resolution,[],[f12472,f50])).

fof(f12472,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2)) ),
    inference(resolution,[],[f12387,f50])).

fof(f12387,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f12386,f26])).

fof(f12386,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f12367,f24])).

fof(f12367,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f12364])).

fof(f12364,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f35,f12345])).

fof(f13321,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2))
    | sP5(sK6(sK0,sK2,sK1),sK2,sK0)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f13290])).

fof(f13290,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2))
    | sP5(sK6(sK0,sK2,sK1),sK2,sK0)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f13240,f12382])).

fof(f13240,plain,(
    ! [X9] :
      ( ~ r2_hidden(k1_xboole_0,X9)
      | ~ r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK2))
      | sP5(sK6(sK0,sK2,sK1),sK2,X9)
      | sK1 = k8_relat_1(sK0,sK2) ) ),
    inference(superposition,[],[f14,f13195])).

fof(f13640,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f13632])).

fof(f13632,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_xboole_0),sK1)
    | sK1 = k8_relat_1(sK0,sK2)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(superposition,[],[f13382,f12372])).

fof(f13382,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK2,sK1),k1_funct_1(sK1,sK6(sK0,sK2,sK1))),sK1)
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f13347,f94])).

fof(f13347,plain,
    ( r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f13344])).

fof(f13344,plain,
    ( sK1 = k8_relat_1(sK0,sK2)
    | r2_hidden(sK6(sK0,sK2,sK1),k1_relat_1(sK1))
    | sK1 = k8_relat_1(sK0,sK2) ),
    inference(resolution,[],[f13341,f22])).

fof(f47,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f16161,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(forward_demodulation,[],[f16142,f15152])).

fof(f15152,plain,(
    k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(subsumption_resolution,[],[f15151,f13764])).

fof(f13764,plain,(
    ! [X0] :
      ( k1_funct_1(sK1,X0) = k1_funct_1(sK2,X0)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f13671,f71])).

fof(f13671,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK1,X0)),sK2)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f13670,f170])).

fof(f15151,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK4)
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4) ),
    inference(subsumption_resolution,[],[f15147,f14934])).

fof(f14934,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(subsumption_resolution,[],[f14933,f14413])).

fof(f14413,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f13931,f16])).

fof(f13931,plain,
    ( sP5(sK3,sK2,sK0)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(trivial_inequality_removal,[],[f13888])).

fof(f13888,plain,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(superposition,[],[f13646,f13764])).

fof(f13646,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f13645])).

fof(f13645,plain,
    ( sK1 != sK1
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0) ),
    inference(backward_demodulation,[],[f21,f13641])).

fof(f14933,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f14923,f50])).

fof(f14923,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK1) ),
    inference(resolution,[],[f14433,f13668])).

fof(f13668,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),sK2)
      | ~ r2_hidden(X7,sK0)
      | r2_hidden(k4_tarski(X6,X7),sK1) ) ),
    inference(subsumption_resolution,[],[f13667,f26])).

fof(f13667,plain,(
    ! [X6,X7] :
      ( r2_hidden(k4_tarski(X6,X7),sK1)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X7,sK0)
      | ~ r2_hidden(k4_tarski(X6,X7),sK2) ) ),
    inference(subsumption_resolution,[],[f13662,f24])).

fof(f13662,plain,(
    ! [X6,X7] :
      ( r2_hidden(k4_tarski(X6,X7),sK1)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(sK1)
      | ~ r2_hidden(X7,sK0)
      | ~ r2_hidden(k4_tarski(X6,X7),sK2) ) ),
    inference(superposition,[],[f46,f13641])).

fof(f14433,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK2)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f14414,f72])).

fof(f14414,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f13931,f15])).

fof(f15147,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK4)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f15112,f13648])).

fof(f13648,plain,
    ( ~ sP5(sK3,sK2,sK0)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4) ),
    inference(trivial_inequality_removal,[],[f13643])).

fof(f13643,plain,
    ( sK1 != sK1
    | ~ sP5(sK3,sK2,sK0)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4) ),
    inference(backward_demodulation,[],[f19,f13641])).

fof(f15112,plain,
    ( sP5(sK3,sK2,sK0)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(subsumption_resolution,[],[f15104,f15037])).

fof(f15037,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f15028,f50])).

fof(f15028,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK2)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f14960,f13670])).

fof(f14960,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(forward_demodulation,[],[f14941,f14280])).

fof(f14280,plain,(
    k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f14278,f14170])).

fof(f14170,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK4)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f14166])).

fof(f14166,plain,
    ( k1_funct_1(sK1,sK4) != k1_funct_1(sK1,sK4)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(superposition,[],[f14107,f13764])).

fof(f14107,plain,
    ( k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f14105,f91])).

fof(f14105,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) != k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f14102,f13648])).

fof(f14102,plain,(
    ! [X0] :
      ( sP5(X0,sK2,sK0)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f14076,f13765])).

fof(f13765,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_relat_1(sK2))
      | k1_xboole_0 = k1_funct_1(sK1,X1) ) ),
    inference(resolution,[],[f13671,f50])).

fof(f14076,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_funct_1(sK1,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | sP5(X0,sK2,sK0) ) ),
    inference(resolution,[],[f14072,f14])).

fof(f14072,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),sK0)
      | k1_xboole_0 = k1_funct_1(sK1,X1) ) ),
    inference(duplicate_literal_removal,[],[f14049])).

fof(f14049,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK2,X1),sK0)
      | k1_xboole_0 = k1_funct_1(sK1,X1)
      | k1_xboole_0 = k1_funct_1(sK1,X1) ) ),
    inference(superposition,[],[f6514,f13842])).

fof(f13842,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,X0) = sK9(sK1,X0)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f13699,f71])).

fof(f13699,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK9(sK1,X0)),sK2)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f13673,f91])).

fof(f13673,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | r2_hidden(k4_tarski(X2,sK9(sK1,X2)),sK2) ) ),
    inference(resolution,[],[f13670,f49])).

fof(f6514,plain,(
    ! [X0] :
      ( r2_hidden(sK9(sK1,X0),sK0)
      | k1_xboole_0 = k1_funct_1(sK1,X0) ) ),
    inference(resolution,[],[f6500,f91])).

fof(f6500,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k1_relat_1(sK1))
      | r2_hidden(sK9(sK1,X2),sK0) ) ),
    inference(resolution,[],[f6497,f49])).

fof(f14278,plain,
    ( k1_xboole_0 != k1_funct_1(sK1,sK4)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f14267])).

fof(f14267,plain,
    ( k1_xboole_0 != k1_funct_1(sK1,sK4)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(superposition,[],[f14107,f14260])).

fof(f14260,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(resolution,[],[f14253,f71])).

fof(f14253,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(resolution,[],[f14252,f13670])).

fof(f14252,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f14248])).

fof(f14248,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(superposition,[],[f14112,f14170])).

fof(f14112,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1)
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(resolution,[],[f14108,f94])).

fof(f14108,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f14106,f91])).

fof(f14106,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK3)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1)) ),
    inference(resolution,[],[f14102,f13649])).

fof(f13649,plain,
    ( ~ sP5(sK3,sK2,sK0)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f13642])).

fof(f13642,plain,
    ( sK1 != sK1
    | ~ sP5(sK3,sK2,sK0)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f18,f13641])).

fof(f14941,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK4)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK1) ),
    inference(resolution,[],[f14934,f94])).

fof(f15104,plain,
    ( k1_xboole_0 = k1_funct_1(sK1,sK4)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | sP5(sK3,sK2,sK0) ),
    inference(resolution,[],[f15099,f14])).

fof(f15099,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(duplicate_literal_removal,[],[f15093])).

fof(f15093,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK1,sK4)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(superposition,[],[f14939,f15079])).

fof(f15079,plain,
    ( k1_funct_1(sK2,sK3) = sK9(sK1,sK3)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f14938,f71])).

fof(f14938,plain,
    ( r2_hidden(k4_tarski(sK3,sK9(sK1,sK3)),sK2)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f14934,f13673])).

fof(f14939,plain,
    ( r2_hidden(sK9(sK1,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f14934,f6500])).

fof(f16142,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1) ),
    inference(resolution,[],[f16128,f94])).

fof(f16128,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f16125,f15966])).

fof(f15966,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f15959,f71])).

fof(f15959,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(k4_tarski(sK4,k1_xboole_0),sK2) ),
    inference(resolution,[],[f15935,f13670])).

fof(f15935,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(forward_demodulation,[],[f15916,f15152])).

fof(f15916,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1) ),
    inference(resolution,[],[f15905,f94])).

fof(f15905,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f15898])).

fof(f15898,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1)) ),
    inference(resolution,[],[f15897,f13737])).

fof(f13737,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1)) ),
    inference(resolution,[],[f13647,f16])).

fof(f13647,plain,
    ( sP5(sK3,sK2,sK0)
    | r2_hidden(sK4,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f13644])).

fof(f13644,plain,
    ( sK1 != sK1
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0) ),
    inference(backward_demodulation,[],[f20,f13641])).

fof(f15897,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f15887,f50])).

fof(f15887,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK1) ),
    inference(resolution,[],[f15183,f13668])).

fof(f15183,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK2)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(backward_demodulation,[],[f14578,f15152])).

fof(f14578,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK2) ),
    inference(resolution,[],[f14538,f72])).

fof(f14538,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | k1_funct_1(sK2,sK4) = k1_funct_1(sK1,sK4) ),
    inference(resolution,[],[f14230,f71])).

fof(f14230,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK2)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f13744,f13670])).

fof(f13744,plain,
    ( r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1)
    | r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f13738,f94])).

fof(f13738,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f13647,f15])).

fof(f16125,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | ~ r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1)) ),
    inference(resolution,[],[f16123,f13649])).

fof(f16123,plain,
    ( sP5(sK3,sK2,sK0)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(subsumption_resolution,[],[f16116,f16043])).

fof(f16043,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(resolution,[],[f16032,f50])).

fof(f16032,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK2)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(resolution,[],[f15994,f13670])).

fof(f15994,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK1)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(forward_demodulation,[],[f15975,f14280])).

fof(f15975,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK1) ),
    inference(resolution,[],[f15966,f94])).

fof(f16116,plain,
    ( k1_xboole_0 = k1_funct_1(sK2,sK4)
    | ~ r2_hidden(sK3,k1_relat_1(sK2))
    | sP5(sK3,sK2,sK0) ),
    inference(resolution,[],[f16109,f14])).

fof(f16109,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(duplicate_literal_removal,[],[f16101])).

fof(f16101,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK2,sK4)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(superposition,[],[f15973,f16082])).

fof(f16082,plain,
    ( k1_funct_1(sK2,sK3) = sK9(sK1,sK3)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(resolution,[],[f15972,f71])).

fof(f15972,plain,
    ( r2_hidden(k4_tarski(sK3,sK9(sK1,sK3)),sK2)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(resolution,[],[f15966,f13673])).

fof(f15973,plain,
    ( r2_hidden(sK9(sK1,sK3),sK0)
    | k1_xboole_0 = k1_funct_1(sK2,sK4) ),
    inference(resolution,[],[f15966,f6500])).

fof(f15153,plain,
    ( k1_xboole_0 != k1_funct_1(sK2,sK4)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | sP5(sK3,sK2,sK0) ),
    inference(backward_demodulation,[],[f13646,f15152])).

fof(f16315,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0) ),
    inference(subsumption_resolution,[],[f16305,f50])).

fof(f16305,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK1) ),
    inference(resolution,[],[f16277,f13668])).

fof(f16277,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK2)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f16275,f72])).

fof(f16275,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f16257,f15])).

fof(f16566,plain,(
    ~ r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f16544,f16256])).

fof(f16256,plain,
    ( ~ sP5(sK3,sK2,sK0)
    | ~ r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f16255])).

fof(f16255,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ sP5(sK3,sK2,sK0)
    | ~ r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f15154,f16212])).

fof(f15154,plain,
    ( ~ sP5(sK3,sK2,sK0)
    | k1_xboole_0 != k1_funct_1(sK2,sK4)
    | ~ r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f13648,f15152])).

fof(f16544,plain,(
    sP5(sK3,sK2,sK0) ),
    inference(resolution,[],[f16535,f15406])).

fof(f15406,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f15405,f6497])).

fof(f15405,plain,
    ( r2_hidden(k4_tarski(sK3,k1_xboole_0),sK1)
    | r2_hidden(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f15386,f14280])).

fof(f15386,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK1,sK3)),sK1) ),
    inference(resolution,[],[f15374,f94])).

fof(f15374,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f15373,f6497])).

fof(f15373,plain,
    ( r2_hidden(k4_tarski(sK4,k1_xboole_0),sK1)
    | r2_hidden(k1_xboole_0,sK0)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f15354,f15152])).

fof(f15354,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k4_tarski(sK4,k1_funct_1(sK1,sK4)),sK1) ),
    inference(resolution,[],[f15350,f94])).

fof(f15350,plain,
    ( r2_hidden(sK4,k1_relat_1(sK1))
    | r2_hidden(k1_xboole_0,sK0)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f15343])).

fof(f15343,plain,
    ( r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k1_xboole_0,sK0)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK4,k1_relat_1(sK1)) ),
    inference(resolution,[],[f15342,f13737])).

fof(f15342,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f15332,f50])).

fof(f15332,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK2,sK3),sK0)
    | r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK1) ),
    inference(resolution,[],[f15206,f13668])).

fof(f15206,plain,
    ( r2_hidden(k4_tarski(sK3,k1_funct_1(sK2,sK3)),sK2)
    | r2_hidden(k1_xboole_0,sK0)
    | r2_hidden(sK3,k1_relat_1(sK1)) ),
    inference(resolution,[],[f15168,f72])).

fof(f15168,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f14231,f15152])).

fof(f14231,plain,
    ( r2_hidden(k1_funct_1(sK1,sK4),sK0)
    | r2_hidden(sK3,k1_relat_1(sK1))
    | r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f13744,f6497])).

fof(f16535,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | sP5(sK3,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f16530,f16386])).

fof(f16386,plain,(
    r2_hidden(sK3,k1_relat_1(sK2)) ),
    inference(resolution,[],[f16355,f50])).

fof(f16355,plain,(
    r2_hidden(k4_tarski(sK3,k1_xboole_0),sK2) ),
    inference(backward_demodulation,[],[f16322,f16343])).

fof(f16343,plain,(
    k1_xboole_0 = sK9(sK1,sK3) ),
    inference(forward_demodulation,[],[f16324,f14280])).

fof(f16324,plain,(
    k1_funct_1(sK1,sK3) = sK9(sK1,sK3) ),
    inference(resolution,[],[f16316,f144])).

fof(f144,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK1))
      | k1_funct_1(sK1,X1) = sK9(sK1,X1) ) ),
    inference(resolution,[],[f93,f49])).

fof(f16322,plain,(
    r2_hidden(k4_tarski(sK3,sK9(sK1,sK3)),sK2) ),
    inference(resolution,[],[f16316,f13673])).

fof(f16530,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | ~ r2_hidden(sK3,k1_relat_1(sK2))
      | sP5(sK3,sK2,X0) ) ),
    inference(superposition,[],[f14,f16385])).

fof(f16385,plain,(
    k1_xboole_0 = k1_funct_1(sK2,sK3) ),
    inference(resolution,[],[f16355,f71])).

%------------------------------------------------------------------------------
