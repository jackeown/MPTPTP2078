%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 210 expanded)
%              Number of leaves         :   12 (  59 expanded)
%              Depth                    :   16
%              Number of atoms          :  231 ( 692 expanded)
%              Number of equality atoms :  107 ( 298 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f540,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f63,f79,f339,f465,f488,f535])).

fof(f535,plain,
    ( spl4_1
    | ~ spl4_16 ),
    inference(avatar_contradiction_clause,[],[f534])).

% (13313)Refutation not found, incomplete strategy% (13313)------------------------------
% (13313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (13313)Termination reason: Refutation not found, incomplete strategy

% (13313)Memory used [KB]: 6268
% (13313)Time elapsed: 0.132 s
% (13313)------------------------------
% (13313)------------------------------
fof(f534,plain,
    ( $false
    | spl4_1
    | ~ spl4_16 ),
    inference(trivial_inequality_removal,[],[f533])).

fof(f533,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_1
    | ~ spl4_16 ),
    inference(superposition,[],[f35,f257])).

fof(f257,plain,
    ( ! [X4] : k1_xboole_0 = X4
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl4_16
  <=> ! [X4] : k1_xboole_0 = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f35,plain,
    ( k1_xboole_0 != sK0
    | spl4_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f488,plain,
    ( spl4_1
    | spl4_16
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f345,f330,f76,f256,f33])).

fof(f76,plain,
    ( spl4_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f330,plain,
    ( spl4_21
  <=> ! [X2] : k1_funct_1(sK1(sK0),sK2(sK0,k1_xboole_0)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f345,plain,
    ( ! [X3] :
        ( k1_xboole_0 = X3
        | k1_xboole_0 = sK0 )
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(superposition,[],[f331,f300])).

fof(f300,plain,
    ( ! [X4] :
        ( k1_xboole_0 = k1_funct_1(sK1(X4),sK2(X4,k1_xboole_0))
        | k1_xboole_0 = X4 )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f282,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f282,plain,(
    ! [X4] :
      ( k1_relat_1(k1_xboole_0) = X4
      | k1_xboole_0 = k1_funct_1(sK1(X4),sK2(X4,k1_xboole_0)) ) ),
    inference(superposition,[],[f31,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = sK3(X0,X1)
      | k1_xboole_0 = k1_funct_1(sK1(X0),sK2(X0,k1_xboole_0)) ) ),
    inference(superposition,[],[f121,f38])).

fof(f38,plain,(
    ! [X2,X1] : k1_xboole_0 = k7_relat_1(sK3(X1,X2),k1_xboole_0) ),
    inference(resolution,[],[f20,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f121,plain,(
    ! [X6,X8,X7] :
      ( sK3(X6,X7) = k7_relat_1(sK3(X6,X7),X8)
      | k1_xboole_0 = k1_funct_1(sK1(X6),sK2(X6,X8)) ) ),
    inference(global_subsumption,[],[f29,f118])).

fof(f118,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(sK3(X6,X7))
      | sK3(X6,X7) = k7_relat_1(sK3(X6,X7),X8)
      | k1_xboole_0 = k1_funct_1(sK1(X6),sK2(X6,X8)) ) ),
    inference(resolution,[],[f45,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 = k1_funct_1(sK1(X0),sK2(X0,X1)) ) ),
    inference(resolution,[],[f21,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f21,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = k1_funct_1(sK1(X0),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f45,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | ~ v1_relat_1(sK3(X2,X3))
      | sK3(X2,X3) = k7_relat_1(sK3(X2,X3),X4) ) ),
    inference(superposition,[],[f25,f31])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f31,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f331,plain,
    ( ! [X2] : k1_funct_1(sK1(sK0),sK2(sK0,k1_xboole_0)) = X2
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f330])).

fof(f465,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f464,f296,f76,f33])).

fof(f296,plain,
    ( spl4_19
  <=> k1_xboole_0 = sK1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f464,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(forward_demodulation,[],[f450,f78])).

fof(f450,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_19 ),
    inference(superposition,[],[f24,f298])).

fof(f298,plain,
    ( k1_xboole_0 = sK1(sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f296])).

fof(f24,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f339,plain,
    ( spl4_19
    | spl4_21 ),
    inference(avatar_split_clause,[],[f338,f330,f296])).

fof(f338,plain,(
    ! [X41] :
      ( k1_funct_1(sK1(sK0),sK2(sK0,k1_xboole_0)) = X41
      | k1_xboole_0 = sK1(sK0) ) ),
    inference(forward_demodulation,[],[f327,f160])).

% (13317)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f160,plain,(
    ! [X0] : sK1(sK0) = sK3(sK0,X0) ),
    inference(equality_resolution,[],[f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK3(X0,X1) = sK1(sK0) ) ),
    inference(equality_resolution,[],[f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | sK0 != X1
      | sK1(X0) = sK3(X1,X2) ) ),
    inference(global_subsumption,[],[f22,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( sK0 != X0
      | ~ v1_relat_1(sK1(X0))
      | sK0 != X1
      | sK1(X0) = sK3(X1,X2) ) ),
    inference(forward_demodulation,[],[f149,f24])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(sK1(X0))
      | sK0 != X1
      | sK0 != k1_relat_1(sK1(X0))
      | sK1(X0) = sK3(X1,X2) ) ),
    inference(resolution,[],[f126,f23])).

fof(f23,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sK0 != X0
      | k1_relat_1(X1) != sK0
      | sK3(X0,X2) = X1 ) ),
    inference(resolution,[],[f50,f29])).

fof(f50,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(sK3(X2,X3))
      | sK0 != X2
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | sK0 != k1_relat_1(X4)
      | sK3(X2,X3) = X4 ) ),
    inference(forward_demodulation,[],[f48,f31])).

fof(f48,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(sK3(X2,X3))
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(X4)
      | sK0 != k1_relat_1(sK3(X2,X3))
      | sK0 != k1_relat_1(X4)
      | sK3(X2,X3) = X4 ) ),
    inference(resolution,[],[f18,f30])).

fof(f30,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != sK0
      | k1_relat_1(X2) != sK0
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f22,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f327,plain,(
    ! [X41] :
      ( k1_xboole_0 = sK1(sK0)
      | k1_funct_1(sK3(sK0,X41),sK2(sK0,k1_xboole_0)) = X41 ) ),
    inference(superposition,[],[f160,f268])).

fof(f268,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = sK3(X0,X1)
      | k1_funct_1(sK3(X0,X2),sK2(X0,k1_xboole_0)) = X2 ) ),
    inference(superposition,[],[f120,f38])).

fof(f120,plain,(
    ! [X4,X2,X5,X3] :
      ( sK3(X2,X3) = k7_relat_1(sK3(X2,X3),X4)
      | k1_funct_1(sK3(X2,X5),sK2(X2,X4)) = X5 ) ),
    inference(global_subsumption,[],[f29,f117])).

fof(f117,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v1_relat_1(sK3(X2,X3))
      | sK3(X2,X3) = k7_relat_1(sK3(X2,X3),X4)
      | k1_funct_1(sK3(X2,X5),sK2(X2,X4)) = X5 ) ),
    inference(resolution,[],[f45,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | k1_funct_1(sK3(X0,X1),sK2(X0,X2)) = X1 ) ),
    inference(resolution,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK3(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f66,f59,f76])).

fof(f59,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f66,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(superposition,[],[f24,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK1(k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f63,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f57,f59])).

fof(f57,plain,(
    k1_xboole_0 = sK1(k1_xboole_0) ),
    inference(superposition,[],[f37,f55])).

fof(f55,plain,(
    ! [X0] : sK1(X0) = k7_relat_1(sK1(X0),X0) ),
    inference(resolution,[],[f46,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | sK1(X0) = k7_relat_1(sK1(X0),X1) ) ),
    inference(global_subsumption,[],[f22,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(sK1(X0))
      | sK1(X0) = k7_relat_1(sK1(X0),X1) ) ),
    inference(superposition,[],[f25,f24])).

% (13301)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(sK1(X0),k1_xboole_0) ),
    inference(resolution,[],[f20,f22])).

fof(f36,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f33])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 17:19:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.51  % (13287)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (13289)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (13295)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (13290)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (13304)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (13287)Refutation not found, incomplete strategy% (13287)------------------------------
% 0.22/0.52  % (13287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13287)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (13287)Memory used [KB]: 1663
% 0.22/0.52  % (13287)Time elapsed: 0.099 s
% 0.22/0.52  % (13287)------------------------------
% 0.22/0.52  % (13287)------------------------------
% 0.22/0.52  % (13291)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (13294)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (13292)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (13303)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (13293)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (13303)Refutation not found, incomplete strategy% (13303)------------------------------
% 0.22/0.53  % (13303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13303)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13303)Memory used [KB]: 6140
% 0.22/0.53  % (13303)Time elapsed: 0.075 s
% 0.22/0.53  % (13303)------------------------------
% 0.22/0.53  % (13303)------------------------------
% 0.22/0.53  % (13296)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (13296)Refutation not found, incomplete strategy% (13296)------------------------------
% 0.22/0.53  % (13296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (13296)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13296)Memory used [KB]: 10618
% 0.22/0.53  % (13296)Time elapsed: 0.107 s
% 0.22/0.53  % (13296)------------------------------
% 0.22/0.53  % (13296)------------------------------
% 0.22/0.53  % (13311)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (13307)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (13297)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (13297)Refutation not found, incomplete strategy% (13297)------------------------------
% 0.22/0.54  % (13297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13297)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13297)Memory used [KB]: 10618
% 0.22/0.54  % (13297)Time elapsed: 0.119 s
% 0.22/0.54  % (13297)------------------------------
% 0.22/0.54  % (13297)------------------------------
% 0.22/0.54  % (13299)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (13302)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (13310)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (13309)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (13305)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (13291)Refutation not found, incomplete strategy% (13291)------------------------------
% 0.22/0.54  % (13291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13291)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13291)Memory used [KB]: 6268
% 0.22/0.54  % (13291)Time elapsed: 0.127 s
% 0.22/0.54  % (13291)------------------------------
% 0.22/0.54  % (13291)------------------------------
% 0.22/0.54  % (13305)Refutation not found, incomplete strategy% (13305)------------------------------
% 0.22/0.54  % (13305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13305)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13305)Memory used [KB]: 10618
% 0.22/0.54  % (13305)Time elapsed: 0.131 s
% 0.22/0.54  % (13305)------------------------------
% 0.22/0.54  % (13305)------------------------------
% 0.22/0.54  % (13309)Refutation not found, incomplete strategy% (13309)------------------------------
% 0.22/0.54  % (13309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (13309)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (13309)Memory used [KB]: 1663
% 0.22/0.54  % (13309)Time elapsed: 0.133 s
% 0.22/0.54  % (13309)------------------------------
% 0.22/0.54  % (13309)------------------------------
% 0.22/0.55  % (13306)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (13315)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (13316)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (13313)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (13288)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (13304)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f540,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f36,f63,f79,f339,f465,f488,f535])).
% 0.22/0.55  fof(f535,plain,(
% 0.22/0.55    spl4_1 | ~spl4_16),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f534])).
% 0.22/0.55  % (13313)Refutation not found, incomplete strategy% (13313)------------------------------
% 0.22/0.55  % (13313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13313)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (13313)Memory used [KB]: 6268
% 0.22/0.55  % (13313)Time elapsed: 0.132 s
% 0.22/0.55  % (13313)------------------------------
% 0.22/0.55  % (13313)------------------------------
% 0.22/0.55  fof(f534,plain,(
% 0.22/0.55    $false | (spl4_1 | ~spl4_16)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f533])).
% 0.22/0.55  fof(f533,plain,(
% 0.22/0.55    k1_xboole_0 != k1_xboole_0 | (spl4_1 | ~spl4_16)),
% 0.22/0.55    inference(superposition,[],[f35,f257])).
% 0.22/0.55  fof(f257,plain,(
% 0.22/0.55    ( ! [X4] : (k1_xboole_0 = X4) ) | ~spl4_16),
% 0.22/0.55    inference(avatar_component_clause,[],[f256])).
% 0.22/0.55  fof(f256,plain,(
% 0.22/0.55    spl4_16 <=> ! [X4] : k1_xboole_0 = X4),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    k1_xboole_0 != sK0 | spl4_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    spl4_1 <=> k1_xboole_0 = sK0),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.55  fof(f488,plain,(
% 0.22/0.55    spl4_1 | spl4_16 | ~spl4_4 | ~spl4_21),
% 0.22/0.55    inference(avatar_split_clause,[],[f345,f330,f76,f256,f33])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    spl4_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.55  fof(f330,plain,(
% 0.22/0.55    spl4_21 <=> ! [X2] : k1_funct_1(sK1(sK0),sK2(sK0,k1_xboole_0)) = X2),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.55  fof(f345,plain,(
% 0.22/0.55    ( ! [X3] : (k1_xboole_0 = X3 | k1_xboole_0 = sK0) ) | (~spl4_4 | ~spl4_21)),
% 0.22/0.55    inference(superposition,[],[f331,f300])).
% 0.22/0.55  fof(f300,plain,(
% 0.22/0.55    ( ! [X4] : (k1_xboole_0 = k1_funct_1(sK1(X4),sK2(X4,k1_xboole_0)) | k1_xboole_0 = X4) ) | ~spl4_4),
% 0.22/0.55    inference(forward_demodulation,[],[f282,f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f76])).
% 0.22/0.55  fof(f282,plain,(
% 0.22/0.55    ( ! [X4] : (k1_relat_1(k1_xboole_0) = X4 | k1_xboole_0 = k1_funct_1(sK1(X4),sK2(X4,k1_xboole_0))) )),
% 0.22/0.55    inference(superposition,[],[f31,f186])).
% 0.22/0.55  fof(f186,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 = sK3(X0,X1) | k1_xboole_0 = k1_funct_1(sK1(X0),sK2(X0,k1_xboole_0))) )),
% 0.22/0.55    inference(superposition,[],[f121,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X2,X1] : (k1_xboole_0 = k7_relat_1(sK3(X1,X2),k1_xboole_0)) )),
% 0.22/0.55    inference(resolution,[],[f20,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).
% 0.22/0.55  fof(f121,plain,(
% 0.22/0.55    ( ! [X6,X8,X7] : (sK3(X6,X7) = k7_relat_1(sK3(X6,X7),X8) | k1_xboole_0 = k1_funct_1(sK1(X6),sK2(X6,X8))) )),
% 0.22/0.55    inference(global_subsumption,[],[f29,f118])).
% 0.22/0.55  fof(f118,plain,(
% 0.22/0.55    ( ! [X6,X8,X7] : (~v1_relat_1(sK3(X6,X7)) | sK3(X6,X7) = k7_relat_1(sK3(X6,X7),X8) | k1_xboole_0 = k1_funct_1(sK1(X6),sK2(X6,X8))) )),
% 0.22/0.55    inference(resolution,[],[f45,f41])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 = k1_funct_1(sK1(X0),sK2(X0,X1))) )),
% 0.22/0.55    inference(resolution,[],[f21,f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.22/0.55    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | k1_xboole_0 = k1_funct_1(sK1(X0),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | ~v1_relat_1(sK3(X2,X3)) | sK3(X2,X3) = k7_relat_1(sK3(X2,X3),X4)) )),
% 0.22/0.55    inference(superposition,[],[f25,f31])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f331,plain,(
% 0.22/0.55    ( ! [X2] : (k1_funct_1(sK1(sK0),sK2(sK0,k1_xboole_0)) = X2) ) | ~spl4_21),
% 0.22/0.55    inference(avatar_component_clause,[],[f330])).
% 0.22/0.55  fof(f465,plain,(
% 0.22/0.55    spl4_1 | ~spl4_4 | ~spl4_19),
% 0.22/0.55    inference(avatar_split_clause,[],[f464,f296,f76,f33])).
% 0.22/0.55  fof(f296,plain,(
% 0.22/0.55    spl4_19 <=> k1_xboole_0 = sK1(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.55  fof(f464,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | (~spl4_4 | ~spl4_19)),
% 0.22/0.55    inference(forward_demodulation,[],[f450,f78])).
% 0.22/0.55  fof(f450,plain,(
% 0.22/0.55    sK0 = k1_relat_1(k1_xboole_0) | ~spl4_19),
% 0.22/0.55    inference(superposition,[],[f24,f298])).
% 0.22/0.55  fof(f298,plain,(
% 0.22/0.55    k1_xboole_0 = sK1(sK0) | ~spl4_19),
% 0.22/0.55    inference(avatar_component_clause,[],[f296])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f339,plain,(
% 0.22/0.55    spl4_19 | spl4_21),
% 0.22/0.55    inference(avatar_split_clause,[],[f338,f330,f296])).
% 0.22/0.55  fof(f338,plain,(
% 0.22/0.55    ( ! [X41] : (k1_funct_1(sK1(sK0),sK2(sK0,k1_xboole_0)) = X41 | k1_xboole_0 = sK1(sK0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f327,f160])).
% 0.22/0.55  % (13317)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    ( ! [X0] : (sK1(sK0) = sK3(sK0,X0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f159])).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    ( ! [X0,X1] : (sK0 != X0 | sK3(X0,X1) = sK1(sK0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f153])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (sK0 != X0 | sK0 != X1 | sK1(X0) = sK3(X1,X2)) )),
% 0.22/0.55    inference(global_subsumption,[],[f22,f152])).
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (sK0 != X0 | ~v1_relat_1(sK1(X0)) | sK0 != X1 | sK1(X0) = sK3(X1,X2)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f149,f24])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(sK1(X0)) | sK0 != X1 | sK0 != k1_relat_1(sK1(X0)) | sK1(X0) = sK3(X1,X2)) )),
% 0.22/0.55    inference(resolution,[],[f126,f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | sK0 != X0 | k1_relat_1(X1) != sK0 | sK3(X0,X2) = X1) )),
% 0.22/0.55    inference(resolution,[],[f50,f29])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X4,X2,X3] : (~v1_relat_1(sK3(X2,X3)) | sK0 != X2 | ~v1_relat_1(X4) | ~v1_funct_1(X4) | sK0 != k1_relat_1(X4) | sK3(X2,X3) = X4) )),
% 0.22/0.55    inference(forward_demodulation,[],[f48,f31])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X4,X2,X3] : (~v1_relat_1(sK3(X2,X3)) | ~v1_relat_1(X4) | ~v1_funct_1(X4) | sK0 != k1_relat_1(sK3(X2,X3)) | sK0 != k1_relat_1(X4) | sK3(X2,X3) = X4) )),
% 0.22/0.55    inference(resolution,[],[f18,f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X1) != sK0 | k1_relat_1(X2) != sK0 | X1 = X2) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(flattening,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,negated_conjecture,(
% 0.22/0.55    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.55    inference(negated_conjecture,[],[f7])).
% 0.22/0.55  fof(f7,conjecture,(
% 0.22/0.55    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  fof(f327,plain,(
% 0.22/0.55    ( ! [X41] : (k1_xboole_0 = sK1(sK0) | k1_funct_1(sK3(sK0,X41),sK2(sK0,k1_xboole_0)) = X41) )),
% 0.22/0.55    inference(superposition,[],[f160,f268])).
% 0.22/0.55  fof(f268,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_xboole_0 = sK3(X0,X1) | k1_funct_1(sK3(X0,X2),sK2(X0,k1_xboole_0)) = X2) )),
% 0.22/0.55    inference(superposition,[],[f120,f38])).
% 0.22/0.55  fof(f120,plain,(
% 0.22/0.55    ( ! [X4,X2,X5,X3] : (sK3(X2,X3) = k7_relat_1(sK3(X2,X3),X4) | k1_funct_1(sK3(X2,X5),sK2(X2,X4)) = X5) )),
% 0.22/0.55    inference(global_subsumption,[],[f29,f117])).
% 0.22/0.55  fof(f117,plain,(
% 0.22/0.55    ( ! [X4,X2,X5,X3] : (~v1_relat_1(sK3(X2,X3)) | sK3(X2,X3) = k7_relat_1(sK3(X2,X3),X4) | k1_funct_1(sK3(X2,X5),sK2(X2,X4)) = X5) )),
% 0.22/0.55    inference(resolution,[],[f45,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | k1_funct_1(sK3(X0,X1),sK2(X0,X2)) = X1) )),
% 0.22/0.55    inference(resolution,[],[f28,f26])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK3(X0,X1),X3) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    spl4_4 | ~spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f66,f59,f76])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    spl4_2 <=> k1_xboole_0 = sK1(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_2),
% 0.22/0.55    inference(superposition,[],[f24,f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    k1_xboole_0 = sK1(k1_xboole_0) | ~spl4_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f59])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    spl4_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f57,f59])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    k1_xboole_0 = sK1(k1_xboole_0)),
% 0.22/0.55    inference(superposition,[],[f37,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0] : (sK1(X0) = k7_relat_1(sK1(X0),X0)) )),
% 0.22/0.55    inference(resolution,[],[f46,f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f27,f26])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | sK1(X0) = k7_relat_1(sK1(X0),X1)) )),
% 0.22/0.55    inference(global_subsumption,[],[f22,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(sK1(X0)) | sK1(X0) = k7_relat_1(sK1(X0),X1)) )),
% 0.22/0.55    inference(superposition,[],[f25,f24])).
% 0.22/0.55  % (13301)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK1(X0),k1_xboole_0)) )),
% 0.22/0.55    inference(resolution,[],[f20,f22])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ~spl4_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f19,f33])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    k1_xboole_0 != sK0),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (13304)------------------------------
% 0.22/0.55  % (13304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (13304)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (13304)Memory used [KB]: 11001
% 0.22/0.55  % (13304)Time elapsed: 0.132 s
% 0.22/0.55  % (13304)------------------------------
% 0.22/0.55  % (13304)------------------------------
% 0.22/0.55  % (13314)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (13308)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (13312)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (13286)Success in time 0.18 s
%------------------------------------------------------------------------------
