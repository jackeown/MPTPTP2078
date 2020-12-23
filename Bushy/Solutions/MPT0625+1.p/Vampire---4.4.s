%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t20_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:21 EDT 2019

% Result     : Theorem 251.75s
% Output     : Refutation 251.75s
% Verified   : 
% Statistics : Number of formulae       :   85 (1274 expanded)
%              Number of leaves         :    4 ( 209 expanded)
%              Depth                    :   37
%              Number of atoms          :  301 (10248 expanded)
%              Number of equality atoms :   67 (1854 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6942,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6940,f6744])).

fof(f6744,plain,(
    r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),sK4(sK0,sK1,sK2)),sK1) ),
    inference(backward_demodulation,[],[f6742,f2523])).

fof(f2523,plain,(
    r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),k1_funct_1(sK2,sK3(sK0,sK1,sK2))),sK1) ),
    inference(forward_demodulation,[],[f2516,f2511])).

fof(f2511,plain,(
    k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1,sK2))) ),
    inference(resolution,[],[f2510,f38])).

fof(f38,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK2))
      | k1_funct_1(sK2,X3) = k1_funct_1(sK1,k1_funct_1(sK0,X3)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(X0,X1) != X2
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X2)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                    & r2_hidden(X4,k1_relat_1(X0)) ) )
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k5_relat_1(X0,X1) != X2
              & ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X2)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X2))
                <=> ( r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                    & r2_hidden(X4,k1_relat_1(X0)) ) )
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( ! [X3] :
                        ( r2_hidden(X3,k1_relat_1(X2))
                       => k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3)) )
                    & ! [X4] :
                        ( r2_hidden(X4,k1_relat_1(X2))
                      <=> ( r2_hidden(k1_funct_1(X0,X4),k1_relat_1(X1))
                          & r2_hidden(X4,k1_relat_1(X0)) ) ) )
                 => k5_relat_1(X0,X1) = X2 ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( ! [X3] :
                        ( r2_hidden(X3,k1_relat_1(X2))
                       => k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3)) )
                    & ! [X3] :
                        ( r2_hidden(X3,k1_relat_1(X2))
                      <=> ( r2_hidden(k1_funct_1(X0,X3),k1_relat_1(X1))
                          & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                 => k5_relat_1(X0,X1) = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( ! [X3] :
                      ( r2_hidden(X3,k1_relat_1(X2))
                     => k1_funct_1(X2,X3) = k1_funct_1(X1,k1_funct_1(X0,X3)) )
                  & ! [X3] :
                      ( r2_hidden(X3,k1_relat_1(X2))
                    <=> ( r2_hidden(k1_funct_1(X0,X3),k1_relat_1(X1))
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
               => k5_relat_1(X0,X1) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t20_funct_1.p',t20_funct_1)).

fof(f2510,plain,(
    r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f2509,f72])).

fof(f72,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t20_funct_1.p',d4_relat_1)).

fof(f2509,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f2508,f687])).

fof(f687,plain,
    ( r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK0))
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(resolution,[],[f258,f72])).

fof(f258,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK6(sK0,sK1,sK2)),sK0)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f257,f41])).

fof(f41,plain,(
    k5_relat_1(sK0,sK1) != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f257,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK6(sK0,sK1,sK2)),sK0)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2)
    | k5_relat_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f139,f39])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f139,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | r2_hidden(k4_tarski(sK3(sK0,sK1,X4),sK6(sK0,sK1,X4)),sK0)
      | r2_hidden(k4_tarski(sK3(sK0,sK1,X4),sK4(sK0,sK1,X4)),X4)
      | k5_relat_1(sK0,sK1) = X4 ) ),
    inference(resolution,[],[f115,f42])).

fof(f42,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f115,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | r2_hidden(k4_tarski(sK3(sK0,X4,X5),sK6(sK0,X4,X5)),sK0)
      | r2_hidden(k4_tarski(sK3(sK0,X4,X5),sK4(sK0,X4,X5)),X5)
      | k5_relat_1(sK0,X4) = X5 ) ),
    inference(resolution,[],[f48,f44])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK6(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t20_funct_1.p',d8_relat_1)).

fof(f2508,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK0))
    | r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f2506,f695])).

fof(f695,plain,
    ( r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK1))
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(resolution,[],[f310,f72])).

fof(f310,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK1)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f309,f41])).

fof(f309,plain,
    ( r2_hidden(k4_tarski(sK6(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK1)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2)
    | k5_relat_1(sK0,sK1) = sK2 ),
    inference(resolution,[],[f163,f39])).

fof(f163,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | r2_hidden(k4_tarski(sK6(sK0,sK1,X4),sK4(sK0,sK1,X4)),sK1)
      | r2_hidden(k4_tarski(sK3(sK0,sK1,X4),sK4(sK0,sK1,X4)),X4)
      | k5_relat_1(sK0,sK1) = X4 ) ),
    inference(resolution,[],[f120,f42])).

fof(f120,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | r2_hidden(k4_tarski(sK6(sK0,X4,X5),sK4(sK0,X4,X5)),X4)
      | r2_hidden(k4_tarski(sK3(sK0,X4,X5),sK4(sK0,X4,X5)),X5)
      | k5_relat_1(sK0,X4) = X5 ) ),
    inference(resolution,[],[f49,f44])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK4(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2506,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK2),k1_relat_1(sK1))
    | ~ r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK0))
    | r2_hidden(sK3(sK0,sK1,sK2),k1_relat_1(sK2))
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(superposition,[],[f37,f692])).

fof(f692,plain,
    ( k1_funct_1(sK0,sK3(sK0,sK1,sK2)) = sK6(sK0,sK1,sK2)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f691,f44])).

fof(f691,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK0)
    | k1_funct_1(sK0,sK3(sK0,sK1,sK2)) = sK6(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f686,f45])).

fof(f45,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f686,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k1_funct_1(sK0,sK3(sK0,sK1,sK2)) = sK6(sK0,sK1,sK2) ),
    inference(resolution,[],[f258,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(subsumption_resolution,[],[f60,f72])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_1__t20_funct_1.p',d4_funct_1)).

fof(f37,plain,(
    ! [X4] :
      ( ~ r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
      | ~ r2_hidden(X4,k1_relat_1(sK0))
      | r2_hidden(X4,k1_relat_1(sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2516,plain,(
    r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),k1_funct_1(sK1,k1_funct_1(sK0,sK3(sK0,sK1,sK2)))),sK1) ),
    inference(resolution,[],[f2510,f100])).

fof(f100,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_relat_1(sK2))
      | r2_hidden(k4_tarski(k1_funct_1(sK0,X1),k1_funct_1(sK1,k1_funct_1(sK0,X1))),sK1) ) ),
    inference(subsumption_resolution,[],[f99,f42])).

fof(f99,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK1)
      | r2_hidden(k4_tarski(k1_funct_1(sK0,X1),k1_funct_1(sK1,k1_funct_1(sK0,X1))),sK1)
      | ~ r2_hidden(X1,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f96,f43])).

fof(f43,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f96,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1)
      | r2_hidden(k4_tarski(k1_funct_1(sK0,X1),k1_funct_1(sK1,k1_funct_1(sK0,X1))),sK1)
      | ~ r2_hidden(X1,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f73,f36])).

fof(f36,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK0,X4),k1_relat_1(sK1))
      | ~ r2_hidden(X4,k1_relat_1(sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6742,plain,(
    k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f6741,f39])).

fof(f6741,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f6735,f40])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f6735,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(duplicate_literal_removal,[],[f6731])).

fof(f6731,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2) ),
    inference(resolution,[],[f6724,f79])).

fof(f6724,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2)
    | k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2) ),
    inference(trivial_inequality_removal,[],[f6722])).

fof(f6722,plain,
    ( sK4(sK0,sK1,sK2) != sK4(sK0,sK1,sK2)
    | k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(superposition,[],[f6721,f700])).

fof(f700,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f699,f42])).

fof(f699,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK6(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f694,f43])).

fof(f694,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k1_funct_1(sK1,sK6(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2) ),
    inference(resolution,[],[f310,f79])).

fof(f6721,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1,sK2)) != sK4(sK0,sK1,sK2)
    | k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2) ),
    inference(inner_rewriting,[],[f6720])).

fof(f6720,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1,sK2)) != sK4(sK0,sK1,sK2)
    | k1_funct_1(sK1,sK6(sK0,sK1,sK2)) = k1_funct_1(sK2,sK3(sK0,sK1,sK2)) ),
    inference(equality_factoring,[],[f6481])).

fof(f6481,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2)
    | k1_funct_1(sK1,sK6(sK0,sK1,sK2)) = k1_funct_1(sK2,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f6480,f39])).

fof(f6480,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1,sK2)) = k1_funct_1(sK2,sK3(sK0,sK1,sK2))
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f6471,f40])).

fof(f6471,plain,
    ( k1_funct_1(sK1,sK6(sK0,sK1,sK2)) = k1_funct_1(sK2,sK3(sK0,sK1,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_funct_1(sK2,sK3(sK0,sK1,sK2)) = sK4(sK0,sK1,sK2) ),
    inference(resolution,[],[f3221,f79])).

fof(f3221,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2)
    | k1_funct_1(sK1,sK6(sK0,sK1,sK2)) = k1_funct_1(sK2,sK3(sK0,sK1,sK2)) ),
    inference(superposition,[],[f2511,f692])).

fof(f6940,plain,(
    ~ r2_hidden(k4_tarski(k1_funct_1(sK0,sK3(sK0,sK1,sK2)),sK4(sK0,sK1,sK2)),sK1) ),
    inference(resolution,[],[f6811,f2515])).

fof(f2515,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),k1_funct_1(sK0,sK3(sK0,sK1,sK2))),sK0) ),
    inference(resolution,[],[f2510,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK0,X0)),sK0) ) ),
    inference(subsumption_resolution,[],[f97,f44])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK0,X0)),sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f95,f45])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK0,X0)),sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f73,f35])).

fof(f35,plain,(
    ! [X4] :
      ( r2_hidden(X4,k1_relat_1(sK0))
      | ~ r2_hidden(X4,k1_relat_1(sK2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f6811,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),X0),sK0)
      | ~ r2_hidden(k4_tarski(X0,sK4(sK0,sK1,sK2)),sK1) ) ),
    inference(subsumption_resolution,[],[f6810,f41])).

fof(f6810,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),X0),sK0)
      | ~ r2_hidden(k4_tarski(X0,sK4(sK0,sK1,sK2)),sK1)
      | k5_relat_1(sK0,sK1) = sK2 ) ),
    inference(subsumption_resolution,[],[f6809,f44])).

fof(f6809,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),X0),sK0)
      | ~ r2_hidden(k4_tarski(X0,sK4(sK0,sK1,sK2)),sK1)
      | ~ v1_relat_1(sK0)
      | k5_relat_1(sK0,sK1) = sK2 ) ),
    inference(subsumption_resolution,[],[f6808,f39])).

fof(f6808,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),X0),sK0)
      | ~ r2_hidden(k4_tarski(X0,sK4(sK0,sK1,sK2)),sK1)
      | ~ v1_relat_1(sK0)
      | k5_relat_1(sK0,sK1) = sK2 ) ),
    inference(subsumption_resolution,[],[f6802,f42])).

fof(f6802,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK2)
      | ~ r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),X0),sK0)
      | ~ r2_hidden(k4_tarski(X0,sK4(sK0,sK1,sK2)),sK1)
      | ~ v1_relat_1(sK0)
      | k5_relat_1(sK0,sK1) = sK2 ) ),
    inference(resolution,[],[f6745,f47])).

fof(f47,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)
      | ~ r2_hidden(k4_tarski(X5,sK4(X0,X1,X2)),X1)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6745,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2)),sK2) ),
    inference(backward_demodulation,[],[f6742,f2525])).

fof(f2525,plain,(
    r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),k1_funct_1(sK2,sK3(sK0,sK1,sK2))),sK2) ),
    inference(subsumption_resolution,[],[f2524,f39])).

fof(f2524,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),k1_funct_1(sK2,sK3(sK0,sK1,sK2))),sK2) ),
    inference(subsumption_resolution,[],[f2519,f40])).

fof(f2519,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK3(sK0,sK1,sK2),k1_funct_1(sK2,sK3(sK0,sK1,sK2))),sK2) ),
    inference(resolution,[],[f2510,f73])).
%------------------------------------------------------------------------------
