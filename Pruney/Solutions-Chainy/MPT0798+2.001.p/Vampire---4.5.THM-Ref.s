%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:07 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 288 expanded)
%              Number of leaves         :    7 (  97 expanded)
%              Depth                    :    9
%              Number of atoms          :  154 (1394 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(subsumption_resolution,[],[f39,f37])).

fof(f37,plain,(
    r3_wellord1(sK1,sK0,k2_funct_1(sK2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f20,f21,f31,f32,f33,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r3_wellord1(X1,X0,k2_funct_1(X2))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_wellord1(X1,X0,k2_funct_1(X2))
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_wellord1(X1,X0,k2_funct_1(X2))
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
               => r3_wellord1(X1,X0,k2_funct_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_wellord1)).

fof(f33,plain,(
    r3_wellord1(sK0,sK1,sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r3_wellord1(X0,X1,sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r3_wellord1(X0,X1,X3)
          & v1_funct_1(X3)
          & v1_relat_1(X3) )
     => ( r3_wellord1(X0,X1,sK2(X0,X1))
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_wellord1)).

fof(f22,plain,(
    r4_wellord1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r4_wellord1(sK1,sK0)
    & r4_wellord1(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r4_wellord1(X1,X0)
            & r4_wellord1(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r4_wellord1(X1,sK0)
          & r4_wellord1(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ~ r4_wellord1(X1,sK0)
        & r4_wellord1(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r4_wellord1(sK1,sK0)
      & r4_wellord1(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r4_wellord1(X1,X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r4_wellord1(X1,X0)
          & r4_wellord1(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r4_wellord1(X0,X1)
             => r4_wellord1(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f32,plain,(
    v1_funct_1(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    v1_relat_1(sK2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f39,plain,(
    ~ r3_wellord1(sK1,sK0,k2_funct_1(sK2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f21,f20,f23,f35,f36,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X1)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    v1_relat_1(k2_funct_1(sK2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f31,f32,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f35,plain,(
    v1_funct_1(k2_funct_1(sK2(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f31,f32,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ~ r4_wellord1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:42:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.42  % (4455)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.19/0.42  % (4455)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(subsumption_resolution,[],[f39,f37])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    r3_wellord1(sK1,sK0,k2_funct_1(sK2(sK0,sK1)))),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f20,f21,f31,f32,f33,f28])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r3_wellord1(X1,X0,k2_funct_1(X2)) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (! [X2] : (r3_wellord1(X1,X0,k2_funct_1(X2)) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(flattening,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (! [X2] : ((r3_wellord1(X1,X0,k2_funct_1(X2)) | ~r3_wellord1(X0,X1,X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r3_wellord1(X0,X1,X2) => r3_wellord1(X1,X0,k2_funct_1(X2))))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_wellord1)).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    r3_wellord1(sK0,sK1,sK2(sK0,sK1))),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f20,f21,f22,f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r3_wellord1(X0,X1,sK2(X0,X1)) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (((r4_wellord1(X0,X1) | ! [X2] : (~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & ((r3_wellord1(X0,X1,sK2(X0,X1)) & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ! [X1,X0] : (? [X3] : (r3_wellord1(X0,X1,X3) & v1_funct_1(X3) & v1_relat_1(X3)) => (r3_wellord1(X0,X1,sK2(X0,X1)) & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (((r4_wellord1(X0,X1) | ! [X2] : (~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & (? [X3] : (r3_wellord1(X0,X1,X3) & v1_funct_1(X3) & v1_relat_1(X3)) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(rectify,[],[f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (((r4_wellord1(X0,X1) | ! [X2] : (~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))) & (? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(nnf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : ((r4_wellord1(X0,X1) <=> ? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) <=> ? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_wellord1)).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    r4_wellord1(sK0,sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    (~r4_wellord1(sK1,sK0) & r4_wellord1(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : (~r4_wellord1(X1,X0) & r4_wellord1(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r4_wellord1(X1,sK0) & r4_wellord1(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ? [X1] : (~r4_wellord1(X1,sK0) & r4_wellord1(sK0,X1) & v1_relat_1(X1)) => (~r4_wellord1(sK1,sK0) & r4_wellord1(sK0,sK1) & v1_relat_1(sK1))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f7,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : (~r4_wellord1(X1,X0) & r4_wellord1(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.42    inference(flattening,[],[f6])).
% 0.19/0.42  fof(f6,plain,(
% 0.19/0.42    ? [X0] : (? [X1] : ((~r4_wellord1(X1,X0) & r4_wellord1(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,negated_conjecture,(
% 0.19/0.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.19/0.42    inference(negated_conjecture,[],[f4])).
% 0.19/0.42  fof(f4,conjecture,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    v1_funct_1(sK2(sK0,sK1))),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f20,f21,f22,f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    v1_relat_1(sK2(sK0,sK1))),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f20,f21,f22,f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    v1_relat_1(sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f15])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    v1_relat_1(sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f15])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    ~r3_wellord1(sK1,sK0,k2_funct_1(sK2(sK0,sK1)))),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f21,f20,f23,f35,f36,f27])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (r4_wellord1(X0,X1) | ~r3_wellord1(X0,X1,X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f36,plain,(
% 0.19/0.42    v1_relat_1(k2_funct_1(sK2(sK0,sK1)))),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f31,f32,f29])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(flattening,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    v1_funct_1(k2_funct_1(sK2(sK0,sK1)))),
% 0.19/0.42    inference(unit_resulting_resolution,[],[f31,f32,f30])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    ~r4_wellord1(sK1,sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f15])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (4455)------------------------------
% 0.19/0.42  % (4455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (4455)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (4455)Memory used [KB]: 9850
% 0.19/0.42  % (4455)Time elapsed: 0.048 s
% 0.19/0.42  % (4455)------------------------------
% 0.19/0.42  % (4455)------------------------------
% 0.19/0.43  % (4449)Success in time 0.074 s
%------------------------------------------------------------------------------
