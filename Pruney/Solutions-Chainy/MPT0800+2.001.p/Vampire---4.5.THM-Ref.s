%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 362 expanded)
%              Number of leaves         :    4 (  66 expanded)
%              Depth                    :   22
%              Number of atoms          :  245 (1693 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f315,plain,(
    $false ),
    inference(subsumption_resolution,[],[f314,f16])).

fof(f16,plain,(
    ~ r4_wellord1(sK0,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(X0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r4_wellord1(X0,X2)
              & r4_wellord1(X1,X2)
              & r4_wellord1(X0,X1)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( v1_relat_1(X2)
               => ( ( r4_wellord1(X1,X2)
                    & r4_wellord1(X0,X1) )
                 => r4_wellord1(X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

fof(f314,plain,(
    r4_wellord1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f313,f18])).

fof(f18,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f313,plain,
    ( ~ v1_relat_1(sK0)
    | r4_wellord1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f312,f57])).

fof(f57,plain,(
    v1_funct_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f55,f31])).

fof(f31,plain,(
    v1_relat_1(sK3(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f30,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,
    ( v1_relat_1(sK3(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f27,f13])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f27,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(sK3(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    r4_wellord1(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(sK3(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).

fof(f55,plain,
    ( ~ v1_relat_1(sK3(sK1,sK2))
    | v1_funct_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) ),
    inference(resolution,[],[f52,f37])).

fof(f37,plain,(
    v1_funct_1(sK3(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f36,f17])).

fof(f36,plain,
    ( v1_funct_1(sK3(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f33,f13])).

fof(f33,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(sK3(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f20,f15])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_funct_1(sK3(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k5_relat_1(sK3(sK0,sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f50,f29])).

fof(f29,plain,(
    v1_relat_1(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f28,f18])).

fof(f28,plain,
    ( v1_relat_1(sK3(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f26,f17])).

fof(f26,plain,
    ( ~ v1_relat_1(sK1)
    | v1_relat_1(sK3(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f19,f14])).

fof(f14,plain,(
    r4_wellord1(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3(sK0,sK1))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k5_relat_1(sK3(sK0,sK1),X0)) ) ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,(
    v1_funct_1(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f34,f18])).

% (25470)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f34,plain,
    ( v1_funct_1(sK3(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f32,f17])).

fof(f32,plain,
    ( ~ v1_relat_1(sK1)
    | v1_funct_1(sK3(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f20,f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f312,plain,
    ( ~ v1_funct_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | r4_wellord1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f311,f45])).

fof(f45,plain,(
    v1_relat_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f43,f31])).

fof(f43,plain,
    ( ~ v1_relat_1(sK3(sK1,sK2))
    | v1_relat_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) ),
    inference(resolution,[],[f39,f37])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(sK3(sK0,sK1),X0)) ) ),
    inference(subsumption_resolution,[],[f38,f29])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK3(sK0,sK1))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k5_relat_1(sK3(sK0,sK1),X0)) ) ),
    inference(resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f311,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))
    | ~ v1_funct_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | r4_wellord1(sK0,sK2) ),
    inference(subsumption_resolution,[],[f306,f13])).

fof(f306,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))
    | ~ v1_funct_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))
    | ~ v1_relat_1(sK0)
    | r4_wellord1(sK0,sK2) ),
    inference(resolution,[],[f304,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X0)
      | r4_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f304,plain,(
    r3_wellord1(sK0,sK2,k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f303,f13])).

fof(f303,plain,
    ( ~ v1_relat_1(sK2)
    | r3_wellord1(sK0,sK2,k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f302,f37])).

fof(f302,plain,
    ( ~ v1_funct_1(sK3(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | r3_wellord1(sK0,sK2,k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f301,f31])).

fof(f301,plain,
    ( ~ v1_relat_1(sK3(sK1,sK2))
    | ~ v1_funct_1(sK3(sK1,sK2))
    | ~ v1_relat_1(sK2)
    | r3_wellord1(sK0,sK2,k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) ),
    inference(resolution,[],[f183,f121])).

fof(f121,plain,(
    r3_wellord1(sK1,sK2,sK3(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f120,f17])).

fof(f120,plain,
    ( r3_wellord1(sK1,sK2,sK3(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f117,f13])).

fof(f117,plain,
    ( ~ v1_relat_1(sK2)
    | r3_wellord1(sK1,sK2,sK3(sK1,sK2))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f21,f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | r3_wellord1(X0,X1,sK3(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ r3_wellord1(sK1,X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r3_wellord1(sK0,X0,k5_relat_1(sK3(sK0,sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f182,f18])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK0)
      | ~ r3_wellord1(sK1,X0,X1)
      | r3_wellord1(sK0,X0,k5_relat_1(sK3(sK0,sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f181,f35])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3(sK0,sK1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK0)
      | ~ r3_wellord1(sK1,X0,X1)
      | r3_wellord1(sK0,X0,k5_relat_1(sK3(sK0,sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f180,f29])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3(sK0,sK1))
      | ~ v1_funct_1(sK3(sK0,sK1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK0)
      | ~ r3_wellord1(sK1,X0,X1)
      | r3_wellord1(sK0,X0,k5_relat_1(sK3(sK0,sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f178,f17])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3(sK0,sK1))
      | ~ v1_funct_1(sK3(sK0,sK1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK0)
      | ~ r3_wellord1(sK1,X0,X1)
      | r3_wellord1(sK0,X0,k5_relat_1(sK3(sK0,sK1),X1)) ) ),
    inference(resolution,[],[f23,f119])).

fof(f119,plain,(
    r3_wellord1(sK0,sK1,sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f118,f18])).

fof(f118,plain,
    ( r3_wellord1(sK0,sK1,sK3(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f116,f17])).

fof(f116,plain,
    ( ~ v1_relat_1(sK1)
    | r3_wellord1(sK0,sK1,sK3(sK0,sK1))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f21,f14])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r3_wellord1(X0,X1,X3)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X0)
      | ~ r3_wellord1(X1,X2,X4)
      | r3_wellord1(X0,X2,k5_relat_1(X3,X4)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
                      | ~ r3_wellord1(X1,X2,X4)
                      | ~ r3_wellord1(X0,X1,X3)
                      | ~ v1_funct_1(X4)
                      | ~ v1_relat_1(X4) )
                  | ~ v1_funct_1(X3)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_wellord1(X0,X2,k5_relat_1(X3,X4))
                      | ~ r3_wellord1(X1,X2,X4)
                      | ~ r3_wellord1(X0,X1,X3)
                      | ~ v1_funct_1(X4)
                      | ~ v1_relat_1(X4) )
                  | ~ v1_funct_1(X3)
                  | ~ v1_relat_1(X3) )
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
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( ( v1_funct_1(X3)
                    & v1_relat_1(X3) )
                 => ! [X4] :
                      ( ( v1_funct_1(X4)
                        & v1_relat_1(X4) )
                     => ( ( r3_wellord1(X1,X2,X4)
                          & r3_wellord1(X0,X1,X3) )
                       => r3_wellord1(X0,X2,k5_relat_1(X3,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_wellord1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n022.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:19:40 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (25463)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.49  % (25463)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (25457)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (25471)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f315,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f314,f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ~r4_wellord1(sK0,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r4_wellord1(X0,X2) & r4_wellord1(X1,X2) & r4_wellord1(X0,X1) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f6])).
% 0.22/0.50  fof(f6,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((~r4_wellord1(X0,X2) & (r4_wellord1(X1,X2) & r4_wellord1(X0,X1))) & v1_relat_1(X2)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r4_wellord1(X1,X2) & r4_wellord1(X0,X1)) => r4_wellord1(X0,X2)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f4])).
% 0.22/0.50  fof(f4,conjecture,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r4_wellord1(X1,X2) & r4_wellord1(X0,X1)) => r4_wellord1(X0,X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).
% 0.22/0.50  fof(f314,plain,(
% 0.22/0.50    r4_wellord1(sK0,sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f313,f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    v1_relat_1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f313,plain,(
% 0.22/0.50    ~v1_relat_1(sK0) | r4_wellord1(sK0,sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f312,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v1_funct_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f55,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    v1_relat_1(sK3(sK1,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f30,f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    v1_relat_1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    v1_relat_1(sK3(sK1,sK2)) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f27,f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    v1_relat_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | v1_relat_1(sK3(sK1,sK2)) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(resolution,[],[f19,f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    r4_wellord1(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(sK3(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r4_wellord1(X0,X1) <=> ? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) <=> ? [X2] : (r3_wellord1(X0,X1,X2) & v1_funct_1(X2) & v1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_wellord1)).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ~v1_relat_1(sK3(sK1,sK2)) | v1_funct_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))),
% 0.22/0.50    inference(resolution,[],[f52,f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    v1_funct_1(sK3(sK1,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f36,f17])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    v1_funct_1(sK3(sK1,sK2)) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f33,f13])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | v1_funct_1(sK3(sK1,sK2)) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(resolution,[],[f20,f15])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | v1_funct_1(sK3(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k5_relat_1(sK3(sK0,sK1),X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f50,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    v1_relat_1(sK3(sK0,sK1))),
% 0.22/0.50    inference(subsumption_resolution,[],[f28,f18])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    v1_relat_1(sK3(sK0,sK1)) | ~v1_relat_1(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f26,f17])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ~v1_relat_1(sK1) | v1_relat_1(sK3(sK0,sK1)) | ~v1_relat_1(sK0)),
% 0.22/0.50    inference(resolution,[],[f19,f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    r4_wellord1(sK0,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f7])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(sK3(sK0,sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k5_relat_1(sK3(sK0,sK1),X0))) )),
% 0.22/0.50    inference(resolution,[],[f25,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    v1_funct_1(sK3(sK0,sK1))),
% 0.22/0.50    inference(subsumption_resolution,[],[f34,f18])).
% 0.22/0.50  % (25470)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    v1_funct_1(sK3(sK0,sK1)) | ~v1_relat_1(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f32,f17])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ~v1_relat_1(sK1) | v1_funct_1(sK3(sK0,sK1)) | ~v1_relat_1(sK0)),
% 0.22/0.50    inference(resolution,[],[f20,f14])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_funct_1(k5_relat_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.22/0.50  fof(f312,plain,(
% 0.22/0.50    ~v1_funct_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) | ~v1_relat_1(sK0) | r4_wellord1(sK0,sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f311,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    v1_relat_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f43,f31])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ~v1_relat_1(sK3(sK1,sK2)) | v1_relat_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))),
% 0.22/0.50    inference(resolution,[],[f39,f37])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k5_relat_1(sK3(sK0,sK1),X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f38,f29])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_relat_1(sK3(sK0,sK1)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k5_relat_1(sK3(sK0,sK1),X0))) )),
% 0.22/0.50    inference(resolution,[],[f35,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_relat_1(k5_relat_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f311,plain,(
% 0.22/0.50    ~v1_relat_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) | ~v1_funct_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) | ~v1_relat_1(sK0) | r4_wellord1(sK0,sK2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f306,f13])).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | ~v1_relat_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) | ~v1_funct_1(k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2))) | ~v1_relat_1(sK0) | r4_wellord1(sK0,sK2)),
% 0.22/0.50    inference(resolution,[],[f304,f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r3_wellord1(X0,X1,X2) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X0) | r4_wellord1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f304,plain,(
% 0.22/0.50    r3_wellord1(sK0,sK2,k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f303,f13])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | r3_wellord1(sK0,sK2,k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f302,f37])).
% 0.22/0.50  fof(f302,plain,(
% 0.22/0.50    ~v1_funct_1(sK3(sK1,sK2)) | ~v1_relat_1(sK2) | r3_wellord1(sK0,sK2,k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f301,f31])).
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    ~v1_relat_1(sK3(sK1,sK2)) | ~v1_funct_1(sK3(sK1,sK2)) | ~v1_relat_1(sK2) | r3_wellord1(sK0,sK2,k5_relat_1(sK3(sK0,sK1),sK3(sK1,sK2)))),
% 0.22/0.50    inference(resolution,[],[f183,f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    r3_wellord1(sK1,sK2,sK3(sK1,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f120,f17])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    r3_wellord1(sK1,sK2,sK3(sK1,sK2)) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(subsumption_resolution,[],[f117,f13])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | r3_wellord1(sK1,sK2,sK3(sK1,sK2)) | ~v1_relat_1(sK1)),
% 0.22/0.50    inference(resolution,[],[f21,f15])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | r3_wellord1(X0,X1,sK3(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r3_wellord1(sK1,X0,X1) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r3_wellord1(sK0,X0,k5_relat_1(sK3(sK0,sK1),X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f182,f18])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK0) | ~r3_wellord1(sK1,X0,X1) | r3_wellord1(sK0,X0,k5_relat_1(sK3(sK0,sK1),X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f181,f35])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(sK3(sK0,sK1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK0) | ~r3_wellord1(sK1,X0,X1) | r3_wellord1(sK0,X0,k5_relat_1(sK3(sK0,sK1),X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f180,f29])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(sK3(sK0,sK1)) | ~v1_funct_1(sK3(sK0,sK1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK0) | ~r3_wellord1(sK1,X0,X1) | r3_wellord1(sK0,X0,k5_relat_1(sK3(sK0,sK1),X1))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f178,f17])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~v1_relat_1(X0) | ~v1_relat_1(sK3(sK0,sK1)) | ~v1_funct_1(sK3(sK0,sK1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK0) | ~r3_wellord1(sK1,X0,X1) | r3_wellord1(sK0,X0,k5_relat_1(sK3(sK0,sK1),X1))) )),
% 0.22/0.50    inference(resolution,[],[f23,f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    r3_wellord1(sK0,sK1,sK3(sK0,sK1))),
% 0.22/0.50    inference(subsumption_resolution,[],[f118,f18])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    r3_wellord1(sK0,sK1,sK3(sK0,sK1)) | ~v1_relat_1(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f116,f17])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ~v1_relat_1(sK1) | r3_wellord1(sK0,sK1,sK3(sK0,sK1)) | ~v1_relat_1(sK0)),
% 0.22/0.50    inference(resolution,[],[f21,f14])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~r3_wellord1(X0,X1,X3) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(X0) | ~r3_wellord1(X1,X2,X4) | r3_wellord1(X0,X2,k5_relat_1(X3,X4))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_wellord1(X0,X2,k5_relat_1(X3,X4)) | ~r3_wellord1(X1,X2,X4) | ~r3_wellord1(X0,X1,X3) | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~v1_funct_1(X3) | ~v1_relat_1(X3)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f9])).
% 0.22/0.50  fof(f9,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r3_wellord1(X0,X2,k5_relat_1(X3,X4)) | (~r3_wellord1(X1,X2,X4) | ~r3_wellord1(X0,X1,X3))) | (~v1_funct_1(X4) | ~v1_relat_1(X4))) | (~v1_funct_1(X3) | ~v1_relat_1(X3))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ! [X3] : ((v1_funct_1(X3) & v1_relat_1(X3)) => ! [X4] : ((v1_funct_1(X4) & v1_relat_1(X4)) => ((r3_wellord1(X1,X2,X4) & r3_wellord1(X0,X1,X3)) => r3_wellord1(X0,X2,k5_relat_1(X3,X4))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_wellord1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (25463)------------------------------
% 0.22/0.50  % (25463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25463)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (25463)Memory used [KB]: 5373
% 0.22/0.50  % (25463)Time elapsed: 0.071 s
% 0.22/0.50  % (25463)------------------------------
% 0.22/0.50  % (25463)------------------------------
% 0.22/0.50  % (25456)Success in time 0.14 s
%------------------------------------------------------------------------------
