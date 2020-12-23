%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1082+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 131 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :  199 ( 481 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f62,f66,f72,f78])).

fof(f78,plain,
    ( spl3_1
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f76,f34])).

fof(f34,plain,
    ( ~ v1_xboole_0(k1_funct_2(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_1
  <=> v1_xboole_0(k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f76,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f75,f20])).

fof(f20,plain,(
    ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
        & ~ v1_xboole_0(X1) )
   => ( ~ m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ m1_funct_2(k1_funct_2(X0,X1),X0,X1)
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => m1_funct_2(k1_funct_2(X0,X1),X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_funct_2)).

fof(f75,plain,
    ( m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    | v1_xboole_0(k1_funct_2(sK0,sK1))
    | spl3_1
    | spl3_4 ),
    inference(resolution,[],[f74,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),X2)
      | m1_funct_2(X2,X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ( ( ~ m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(sK2(X0,X1,X2),X0,X1)
              | ~ v1_funct_1(sK2(X0,X1,X2)) )
            & m1_subset_1(sK2(X0,X1,X2),X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & m1_subset_1(X3,X2) )
     => ( ( ~ m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(sK2(X0,X1,X2),X0,X1)
          | ~ v1_funct_1(sK2(X0,X1,X2)) )
        & m1_subset_1(sK2(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X4,X0,X1)
                & v1_funct_1(X4) )
              | ~ m1_subset_1(X4,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(rectify,[],[f15])).

% (24636)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_funct_2(X2,X0,X1)
          | ? [X3] :
              ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X3,X0,X1)
                | ~ v1_funct_1(X3) )
              & m1_subset_1(X3,X2) ) )
        & ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
              | ~ m1_subset_1(X3,X2) )
          | ~ m1_funct_2(X2,X0,X1) ) )
      | v1_xboole_0(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
            | ~ m1_subset_1(X3,X2) ) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ( m1_funct_2(X2,X0,X1)
      <=> ! [X3] :
            ( m1_subset_1(X3,X2)
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_2)).

fof(f74,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f73,f34])).

fof(f73,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | spl3_4 ),
    inference(resolution,[],[f55,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f55,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | spl3_4 ),
    inference(resolution,[],[f47,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

fof(f47,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_4
  <=> m1_subset_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f70,f34])).

fof(f70,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f69,f20])).

fof(f69,plain,
    ( m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    | v1_xboole_0(k1_funct_2(sK0,sK1))
    | spl3_1
    | spl3_3 ),
    inference(resolution,[],[f68,f26])).

fof(f68,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f67,f34])).

fof(f67,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | spl3_3 ),
    inference(resolution,[],[f52,f22])).

fof(f52,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(sK0,sK1))
    | spl3_3 ),
    inference(resolution,[],[f43,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,
    ( ~ v1_funct_2(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_3
  <=> v1_funct_2(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f66,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f64,f19])).

fof(f19,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,
    ( v1_xboole_0(sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f35,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_funct_2(X0,X1))
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_funct_2)).

fof(f35,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f62,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f60,f20])).

fof(f60,plain,
    ( m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    | spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f59,f34])).

fof(f59,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    | spl3_2 ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,
    ( v1_xboole_0(k1_funct_2(sK0,sK1))
    | m1_funct_2(k1_funct_2(sK0,sK1),sK0,sK1)
    | v1_xboole_0(k1_funct_2(sK0,sK1))
    | spl3_2 ),
    inference(resolution,[],[f53,f26])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(X0,X1))
        | v1_xboole_0(k1_funct_2(X0,X1)) )
    | spl3_2 ),
    inference(resolution,[],[f50,f22])).

fof(f50,plain,
    ( ! [X4,X3] : ~ r2_hidden(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_funct_2(X3,X4))
    | spl3_2 ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(X2)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,
    ( ~ v1_funct_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_2
  <=> v1_funct_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f31,f45,f41,f37,f33])).

fof(f31,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2(sK0,sK1,k1_funct_2(sK0,sK1)),sK0,sK1)
    | ~ v1_funct_1(sK2(sK0,sK1,k1_funct_2(sK0,sK1)))
    | v1_xboole_0(k1_funct_2(sK0,sK1)) ),
    inference(resolution,[],[f27,f20])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2(X0,X1,X2),X0,X1)
      | ~ v1_funct_1(sK2(X0,X1,X2))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
