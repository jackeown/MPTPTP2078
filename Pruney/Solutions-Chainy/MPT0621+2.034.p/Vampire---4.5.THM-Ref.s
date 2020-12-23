%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 583 expanded)
%              Number of leaves         :    9 ( 154 expanded)
%              Depth                    :   19
%              Number of atoms          :  266 (4293 expanded)
%              Number of equality atoms :  107 (1112 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f780,plain,(
    $false ),
    inference(subsumption_resolution,[],[f629,f488])).

fof(f488,plain,(
    ! [X2,X1] : X1 = X2 ),
    inference(superposition,[],[f485,f485])).

fof(f485,plain,(
    ! [X0,X1] : k1_funct_1(sK1(sK0),sK3(X1,X1,sK0)) = X0 ),
    inference(subsumption_resolution,[],[f484,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( k1_xboole_0 != sK0
    & ! [X1] :
        ( ! [X2] :
            ( X1 = X2
            | k1_relat_1(X2) != sK0
            | k1_relat_1(X1) != sK0
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & ! [X1] :
            ( ! [X2] :
                ( X1 = X2
                | k1_relat_1(X2) != X0
                | k1_relat_1(X1) != X0
                | ~ v1_funct_1(X2)
                | ~ v1_relat_1(X2) )
            | ~ v1_funct_1(X1)
            | ~ v1_relat_1(X1) ) )
   => ( k1_xboole_0 != sK0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != sK0
              | k1_relat_1(X1) != sK0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(f484,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK0
      | k1_funct_1(sK1(sK0),sK3(X1,X1,sK0)) = X0 ) ),
    inference(forward_demodulation,[],[f483,f166])).

fof(f166,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(subsumption_resolution,[],[f164,f85])).

fof(f85,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(sK3(X7,X7,k1_xboole_0),X8)
      | k1_xboole_0 = k4_xboole_0(X7,X7) ) ),
    inference(resolution,[],[f74,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f40,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f40,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f74,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X2) = X3
      | r2_hidden(sK3(X2,X2,X3),X3)
      | r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(resolution,[],[f37,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f164,plain,(
    ! [X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X1)
      | r2_hidden(sK3(X1,X1,k1_xboole_0),X1) ) ),
    inference(duplicate_literal_removal,[],[f154])).

fof(f154,plain,(
    ! [X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X1)
      | r2_hidden(sK3(X1,X1,k1_xboole_0),X1)
      | k1_xboole_0 = k4_xboole_0(X1,X1) ) ),
    inference(resolution,[],[f85,f36])).

fof(f483,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK1(sK0),sK3(X1,X1,sK0)) = X0
      | sK0 = k4_xboole_0(X1,X1) ) ),
    inference(superposition,[],[f87,f425])).

fof(f425,plain,(
    ! [X0] : sK1(sK0) = sK2(sK0,X0) ),
    inference(equality_resolution,[],[f408])).

fof(f408,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK2(X0,X1) = sK1(sK0) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X4
      | sK2(X2,X3) = sK1(X4)
      | sK0 != X2 ) ),
    inference(subsumption_resolution,[],[f110,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK2(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK2(X0,X1)) = X0
      & v1_funct_1(sK2(X0,X1))
      & v1_relat_1(sK2(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK2(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f110,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | sK2(X2,X3) = sK1(X4)
      | sK0 != X4
      | ~ v1_relat_1(sK2(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f107,f30])).

fof(f30,plain,(
    ! [X0,X1] : v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f107,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | sK2(X2,X3) = sK1(X4)
      | sK0 != X4
      | ~ v1_funct_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3)) ) ),
    inference(superposition,[],[f79,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK0
      | sK1(X0) = X1
      | sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f78,f25])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f14])).

% (29239)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f14,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK1(X0)) = X0
      & v1_funct_1(sK1(X0))
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK1(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK1(X0)) = X0
        & v1_funct_1(sK1(X0))
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK1(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(sK1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f76,f26])).

fof(f26,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK1(X0) = X1
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(sK1(X0))
      | ~ v1_relat_1(sK1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f22,f27])).

fof(f27,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | X1 = X2
      | k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,(
    ! [X14,X12,X13] :
      ( k1_funct_1(sK2(X13,X14),sK3(X12,X12,X13)) = X14
      | k4_xboole_0(X12,X12) = X13 ) ),
    inference(resolution,[],[f74,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK2(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f629,plain,(
    ! [X0] : k1_xboole_0 != X0 ),
    inference(superposition,[],[f23,f488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (29251)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (29245)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (29255)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (29245)Refutation not found, incomplete strategy% (29245)------------------------------
% 0.22/0.53  % (29245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (29245)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (29245)Memory used [KB]: 10618
% 0.22/0.53  % (29245)Time elapsed: 0.104 s
% 0.22/0.53  % (29245)------------------------------
% 0.22/0.53  % (29245)------------------------------
% 0.22/0.54  % (29254)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.54  % (29242)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.55  % (29247)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (29241)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.55  % (29243)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.55  % (29255)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f780,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(subsumption_resolution,[],[f629,f488])).
% 0.22/0.55  fof(f488,plain,(
% 0.22/0.55    ( ! [X2,X1] : (X1 = X2) )),
% 0.22/0.55    inference(superposition,[],[f485,f485])).
% 0.22/0.55  fof(f485,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_funct_1(sK1(sK0),sK3(X1,X1,sK0)) = X0) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f484,f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    k1_xboole_0 != sK0),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) => (k1_xboole_0 != sK0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != sK0 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(flattening,[],[f7])).
% 0.22/0.55  fof(f7,plain,(
% 0.22/0.55    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,negated_conjecture,(
% 0.22/0.55    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.55    inference(negated_conjecture,[],[f5])).
% 0.22/0.55  fof(f5,conjecture,(
% 0.22/0.55    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).
% 0.22/0.55  fof(f484,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = sK0 | k1_funct_1(sK1(sK0),sK3(X1,X1,sK0)) = X0) )),
% 0.22/0.55    inference(forward_demodulation,[],[f483,f166])).
% 0.22/0.55  fof(f166,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f164,f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X8,X7] : (~r2_hidden(sK3(X7,X7,k1_xboole_0),X8) | k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 0.22/0.55    inference(resolution,[],[f74,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.55    inference(superposition,[],[f40,f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.55    inference(rectify,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.55    inference(flattening,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.22/0.55    inference(nnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X2,X3] : (r2_hidden(sK3(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = X3 | r2_hidden(sK3(X2,X2,X3),X3) | r2_hidden(sK3(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3) )),
% 0.22/0.55    inference(resolution,[],[f37,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f164,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1) | r2_hidden(sK3(X1,X1,k1_xboole_0),X1)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f154])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1) | r2_hidden(sK3(X1,X1,k1_xboole_0),X1) | k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.22/0.55    inference(resolution,[],[f85,f36])).
% 0.22/0.55  fof(f483,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_funct_1(sK1(sK0),sK3(X1,X1,sK0)) = X0 | sK0 = k4_xboole_0(X1,X1)) )),
% 0.22/0.55    inference(superposition,[],[f87,f425])).
% 0.22/0.55  fof(f425,plain,(
% 0.22/0.55    ( ! [X0] : (sK1(sK0) = sK2(sK0,X0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f408])).
% 0.22/0.55  fof(f408,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sK0 != X0 | sK2(X0,X1) = sK1(sK0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f111])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    ( ! [X4,X2,X3] : (sK0 != X4 | sK2(X2,X3) = sK1(X4) | sK0 != X2) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f110,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.22/0.55  fof(f110,plain,(
% 0.22/0.55    ( ! [X4,X2,X3] : (sK0 != X2 | sK2(X2,X3) = sK1(X4) | sK0 != X4 | ~v1_relat_1(sK2(X2,X3))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f107,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f107,plain,(
% 0.22/0.55    ( ! [X4,X2,X3] : (sK0 != X2 | sK2(X2,X3) = sK1(X4) | sK0 != X4 | ~v1_funct_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3))) )),
% 0.22/0.55    inference(superposition,[],[f79,f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | sK1(X0) = X1 | sK0 != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f78,f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  % (29239)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f9,f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK1(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK1(X0)) = X0 & v1_funct_1(sK1(X0)) & v1_relat_1(sK1(X0))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sK0 != X0 | sK1(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_relat_1(sK1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f76,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sK0 != X0 | sK1(X0) = X1 | k1_relat_1(X1) != sK0 | ~v1_funct_1(sK1(X0)) | ~v1_relat_1(sK1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(superposition,[],[f22,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f14])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | X1 = X2 | k1_relat_1(X1) != sK0 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    ( ! [X14,X12,X13] : (k1_funct_1(sK2(X13,X14),sK3(X12,X12,X13)) = X14 | k4_xboole_0(X12,X12) = X13) )),
% 0.22/0.55    inference(resolution,[],[f74,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK2(X0,X1),X3) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f629,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 != X0) )),
% 0.22/0.55    inference(superposition,[],[f23,f488])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (29255)------------------------------
% 0.22/0.55  % (29255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (29255)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (29255)Memory used [KB]: 1918
% 0.22/0.55  % (29255)Time elapsed: 0.130 s
% 0.22/0.55  % (29255)------------------------------
% 0.22/0.55  % (29255)------------------------------
% 0.22/0.56  % (29238)Success in time 0.188 s
%------------------------------------------------------------------------------
