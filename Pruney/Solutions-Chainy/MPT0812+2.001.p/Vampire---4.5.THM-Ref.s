%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 718 expanded)
%              Number of leaves         :    7 ( 242 expanded)
%              Depth                    :    9
%              Number of atoms          :  265 (4277 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f54])).

fof(f54,plain,(
    v1_relat_2(sK1) ),
    inference(unit_resulting_resolution,[],[f21,f22,f41,f46,f47,f48,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_2(X1)
      | ~ v1_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_wellord1(X1)
                  | ~ v1_wellord1(X0) )
                & ( v4_relat_2(X1)
                  | ~ v4_relat_2(X0) )
                & ( v6_relat_2(X1)
                  | ~ v6_relat_2(X0) )
                & ( v8_relat_2(X1)
                  | ~ v8_relat_2(X0) )
                & ( v1_relat_2(X1)
                  | ~ v1_relat_2(X0) ) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ( ( v1_wellord1(X0)
                   => v1_wellord1(X1) )
                  & ( v4_relat_2(X0)
                   => v4_relat_2(X1) )
                  & ( v6_relat_2(X0)
                   => v6_relat_2(X1) )
                  & ( v8_relat_2(X0)
                   => v8_relat_2(X1) )
                  & ( v1_relat_2(X0)
                   => v1_relat_2(X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).

fof(f48,plain,(
    r3_wellord1(sK0,sK1,sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f22,f23,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r3_wellord1(X0,X1,sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ( r3_wellord1(X0,X1,sK2(X0,X1))
                & v1_funct_1(sK2(X0,X1))
                & v1_relat_1(sK2(X0,X1)) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK2(X0,X1))
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X3] :
                  ( r3_wellord1(X0,X1,X3)
                  & v1_funct_1(X3)
                  & v1_relat_1(X3) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r4_wellord1(X0,X1)
              | ! [X2] :
                  ( ~ r3_wellord1(X0,X1,X2)
                  | ~ v1_funct_1(X2)
                  | ~ v1_relat_1(X2) ) )
            & ( ? [X2] :
                  ( r3_wellord1(X0,X1,X2)
                  & v1_funct_1(X2)
                  & v1_relat_1(X2) )
              | ~ r4_wellord1(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
          <=> ? [X2] :
                ( r3_wellord1(X0,X1,X2)
                & v1_funct_1(X2)
                & v1_relat_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

fof(f23,plain,(
    r4_wellord1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v2_wellord1(sK1)
    & v2_wellord1(sK0)
    & r4_wellord1(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_wellord1(X1)
            & v2_wellord1(X0)
            & r4_wellord1(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(sK0)
          & r4_wellord1(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ~ v2_wellord1(X1)
        & v2_wellord1(sK0)
        & r4_wellord1(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ v2_wellord1(sK1)
      & v2_wellord1(sK0)
      & r4_wellord1(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_wellord1(X1)
          & v2_wellord1(X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( v2_wellord1(X0)
                & r4_wellord1(X0,X1) )
             => v2_wellord1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( v2_wellord1(X0)
              & r4_wellord1(X0,X1) )
           => v2_wellord1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_wellord1)).

fof(f47,plain,(
    v1_funct_1(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f22,f23,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    v1_relat_1(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f22,f23,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,(
    v1_relat_2(sK0) ),
    inference(unit_resulting_resolution,[],[f21,f24,f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

fof(f24,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ~ v1_relat_2(sK1) ),
    inference(unit_resulting_resolution,[],[f22,f50,f51,f52,f25,f53,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_wellord1(X0)
      | v2_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f53,plain,(
    v8_relat_2(sK1) ),
    inference(unit_resulting_resolution,[],[f21,f22,f42,f46,f47,f48,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v8_relat_2(X1)
      | ~ v8_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    v8_relat_2(sK0) ),
    inference(unit_resulting_resolution,[],[f21,f24,f27])).

fof(f27,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ~ v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    v6_relat_2(sK1) ),
    inference(unit_resulting_resolution,[],[f21,f22,f44,f46,f47,f48,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v6_relat_2(X1)
      | ~ v6_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    v6_relat_2(sK0) ),
    inference(unit_resulting_resolution,[],[f21,f24,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    v4_relat_2(sK1) ),
    inference(unit_resulting_resolution,[],[f21,f22,f43,f46,f47,f48,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_2(X1)
      | ~ v4_relat_2(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    v4_relat_2(sK0) ),
    inference(unit_resulting_resolution,[],[f21,f24,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f50,plain,(
    v1_wellord1(sK1) ),
    inference(unit_resulting_resolution,[],[f21,f22,f45,f46,f47,f48,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_wellord1(X1)
      | ~ v1_wellord1(X0)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    v1_wellord1(sK0) ),
    inference(unit_resulting_resolution,[],[f21,f24,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:58:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (31135)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.47  % (31136)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.21/0.47  % (31136)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    v1_relat_2(sK1)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f22,f41,f46,f47,f48,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_relat_2(X1) | ~v1_relat_2(X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (((v1_wellord1(X1) | ~v1_wellord1(X0)) & (v4_relat_2(X1) | ~v4_relat_2(X0)) & (v6_relat_2(X1) | ~v6_relat_2(X0)) & (v8_relat_2(X1) | ~v8_relat_2(X0)) & (v1_relat_2(X1) | ~v1_relat_2(X0))) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((((v1_wellord1(X1) | ~v1_wellord1(X0)) & (v4_relat_2(X1) | ~v4_relat_2(X0)) & (v6_relat_2(X1) | ~v6_relat_2(X0)) & (v8_relat_2(X1) | ~v8_relat_2(X0)) & (v1_relat_2(X1) | ~v1_relat_2(X0))) | ~r3_wellord1(X0,X1,X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => ((v1_wellord1(X0) => v1_wellord1(X1)) & (v4_relat_2(X0) => v4_relat_2(X1)) & (v6_relat_2(X0) => v6_relat_2(X1)) & (v8_relat_2(X0) => v8_relat_2(X1)) & (v1_relat_2(X0) => v1_relat_2(X1)))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_wellord1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    r3_wellord1(sK0,sK1,sK2(sK0,sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f22,f23,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r3_wellord1(X0,X1,sK2(X0,X1)) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((r4_wellord1(X0,X1) | ! [X2] : (~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & ((r3_wellord1(X0,X1,sK2(X0,X1)) & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X1,X0] : (? [X3] : (r3_wellord1(X0,X1,X3) & v1_funct_1(X3) & v1_relat_1(X3)) => (r3_wellord1(X0,X1,sK2(X0,X1)) & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((r4_wellord1(X0,X1) | ! [X2] : (~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & (? [X3] : (r3_wellord1(X0,X1,X3) & v1_funct_1(X3) & v1_relat_1(X3)) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(rectify,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((r4_wellord1(X0,X1) | ! [X2] : (~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & (? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r4_wellord1(X0,X1) <=> ? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) <=> ? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    r4_wellord1(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    (~v2_wellord1(sK1) & v2_wellord1(sK0) & r4_wellord1(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~v2_wellord1(X1) & v2_wellord1(X0) & r4_wellord1(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~v2_wellord1(X1) & v2_wellord1(sK0) & r4_wellord1(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X1] : (~v2_wellord1(X1) & v2_wellord1(sK0) & r4_wellord1(sK0,X1) & v1_relat_1(X1)) => (~v2_wellord1(sK1) & v2_wellord1(sK0) & r4_wellord1(sK0,sK1) & v1_relat_1(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~v2_wellord1(X1) & v2_wellord1(X0) & r4_wellord1(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~v2_wellord1(X1) & (v2_wellord1(X0) & r4_wellord1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((v2_wellord1(X0) & r4_wellord1(X0,X1)) => v2_wellord1(X1))))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((v2_wellord1(X0) & r4_wellord1(X0,X1)) => v2_wellord1(X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_wellord1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    v1_funct_1(sK2(sK0,sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f22,f23,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v1_relat_1(sK2(sK0,sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f22,f23,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    v1_relat_2(sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f24,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : (((v2_wellord1(X0) | ~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0)) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (((v2_wellord1(X0) | (~v1_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0))) & ((v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0)) | ~v2_wellord1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : ((v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) <=> (v1_wellord1(X0) & v6_relat_2(X0) & v4_relat_2(X0) & v8_relat_2(X0) & v1_relat_2(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    v2_wellord1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~v1_relat_2(sK1)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f22,f50,f51,f52,f25,f53,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_wellord1(X0) | v2_wellord1(X0) | ~v6_relat_2(X0) | ~v4_relat_2(X0) | ~v8_relat_2(X0) | ~v1_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    v8_relat_2(sK1)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f22,f42,f46,f47,f48,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v8_relat_2(X1) | ~v8_relat_2(X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    v8_relat_2(sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f24,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (v8_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ~v2_wellord1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    v6_relat_2(sK1)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f22,f44,f46,f47,f48,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v6_relat_2(X1) | ~v6_relat_2(X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    v6_relat_2(sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f24,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0] : (v6_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    v4_relat_2(sK1)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f22,f43,f46,f47,f48,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v4_relat_2(X1) | ~v4_relat_2(X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    v4_relat_2(sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f24,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (v4_relat_2(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    v1_wellord1(sK1)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f22,f45,f46,f47,f48,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_wellord1(X1) | ~v1_wellord1(X0) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    v1_wellord1(sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f21,f24,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0] : (v1_wellord1(X0) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (31136)------------------------------
% 0.21/0.47  % (31136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (31136)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (31136)Memory used [KB]: 9850
% 0.21/0.47  % (31136)Time elapsed: 0.050 s
% 0.21/0.47  % (31136)------------------------------
% 0.21/0.47  % (31136)------------------------------
% 0.21/0.47  % (31130)Success in time 0.115 s
%------------------------------------------------------------------------------
