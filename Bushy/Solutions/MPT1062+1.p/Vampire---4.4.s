%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t179_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:37 EDT 2019

% Result     : Theorem 7.69s
% Output     : Refutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 556 expanded)
%              Number of leaves         :   19 ( 129 expanded)
%              Depth                    :   11
%              Number of atoms          :  404 (3482 expanded)
%              Number of equality atoms :   15 (  34 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f477,f504,f536,f643,f647,f651,f1407,f4043,f4232,f4299])).

fof(f4299,plain,(
    ~ spl10_116 ),
    inference(avatar_contradiction_clause,[],[f4291])).

fof(f4291,plain,
    ( $false
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f42,f125,f824,f4231])).

fof(f4231,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK0,sK1,sK2,sK3,sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),X0)
        | r2_hidden(sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)),k6_funct_2(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) )
    | ~ spl10_116 ),
    inference(avatar_component_clause,[],[f4230])).

fof(f4230,plain,
    ( spl10_116
  <=> ! [X0] :
        ( r2_hidden(sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)),k6_funct_2(sK0,sK1,sK2,X0))
        | ~ r2_hidden(sK7(sK0,sK1,sK2,sK3,sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f824,plain,(
    r2_hidden(sK7(sK0,sK1,sK2,sK3,sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),sK4) ),
    inference(unit_resulting_resolution,[],[f43,f355,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t179_funct_2.p',d3_tarski)).

fof(f355,plain,(
    r2_hidden(sK7(sK0,sK1,sK2,sK3,sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),sK3) ),
    inference(unit_resulting_resolution,[],[f49,f50,f47,f45,f48,f111,f124,f199,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(sK2,X1,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k6_funct_2(X1,X0,sK2,X2),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
      | r2_hidden(sK7(X1,X0,sK2,X2,X3),X2)
      | ~ r2_hidden(X3,k6_funct_2(X1,X0,sK2,X2)) ) ),
    inference(resolution,[],[f46,f78])).

fof(f78,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | r2_hidden(sK7(X0,X1,X2,X3,X5),X3)
      | ~ r2_hidden(X5,k6_funct_2(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | r2_hidden(sK7(X0,X1,X2,X3,X5),X3)
      | ~ r2_hidden(X5,X4)
      | k6_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) )
                            | ~ m1_subset_1(X5,k1_zfmisc_1(X0)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
                     => ( k6_funct_2(X0,X1,X2,X3) = X4
                      <=> ! [X5] :
                            ( m1_subset_1(X5,k1_zfmisc_1(X0))
                           => ( r2_hidden(X5,X4)
                            <=> ? [X6] :
                                  ( k8_relset_1(X0,X1,X2,X6) = X5
                                  & r2_hidden(X6,X3)
                                  & m1_subset_1(X6,k1_zfmisc_1(X1)) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t179_funct_2.p',d10_funct_2)).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
                      & r1_tarski(X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4))
                      & r1_tarski(X3,X4)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1))) )
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                       => ( r1_tarski(X3,X4)
                         => r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X1)))
                     => ( r1_tarski(X3,X4)
                       => r1_tarski(k6_funct_2(X0,X1,X2,X3),k6_funct_2(X0,X1,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t179_funct_2.p',t179_funct_2)).

fof(f199,plain,(
    m1_subset_1(sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f111,f124,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t179_funct_2.p',t4_subset)).

fof(f124,plain,(
    r2_hidden(sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)),k6_funct_2(sK0,sK1,sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f44,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ~ r1_tarski(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,(
    m1_subset_1(k6_funct_2(sK0,sK1,sK2,sK3),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f50,f46,f49,f45,f47,f48,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t179_funct_2.p',dt_k6_funct_2)).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f125,plain,(
    ~ r2_hidden(sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)),k6_funct_2(sK0,sK1,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f44,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f4232,plain,
    ( ~ spl10_109
    | spl10_116
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f1435,f1405,f4230,f3956])).

fof(f3956,plain,
    ( spl10_109
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_109])])).

fof(f1405,plain,
    ( spl10_40
  <=> ! [X3,X4] :
        ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X3),k6_funct_2(sK0,sK1,sK2,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK1)))
        | ~ r2_hidden(X3,X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f1435,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)),k6_funct_2(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
        | ~ r2_hidden(sK7(sK0,sK1,sK2,sK3,sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),X0)
        | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),k1_zfmisc_1(sK1)) )
    | ~ spl10_40 ),
    inference(superposition,[],[f1406,f356])).

fof(f356,plain,(
    k8_relset_1(sK0,sK1,sK2,sK7(sK0,sK1,sK2,sK3,sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)))) = sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f49,f50,f47,f45,f48,f111,f124,f199,f81])).

fof(f81,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ v1_funct_2(sK2,X5,X4)
      | v1_xboole_0(X5)
      | v1_xboole_0(X4)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X5,X4)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X4)))
      | ~ m1_subset_1(k6_funct_2(X5,X4,sK2,X6),k1_zfmisc_1(k1_zfmisc_1(X5)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X5))
      | k8_relset_1(X5,X4,sK2,sK7(X5,X4,sK2,X6,X7)) = X7
      | ~ r2_hidden(X7,k6_funct_2(X5,X4,sK2,X6)) ) ),
    inference(resolution,[],[f46,f77])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X1,X2,sK7(X0,X1,X2,X3,X5)) = X5
      | ~ r2_hidden(X5,k6_funct_2(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X1,X2,sK7(X0,X1,X2,X3,X5)) = X5
      | ~ r2_hidden(X5,X4)
      | k6_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1406,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X3),k6_funct_2(sK0,sK1,sK2,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK1)))
        | ~ r2_hidden(X3,X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK1)) )
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f1405])).

fof(f4043,plain,(
    spl10_109 ),
    inference(avatar_contradiction_clause,[],[f4028])).

fof(f4028,plain,
    ( $false
    | ~ spl10_109 ),
    inference(unit_resulting_resolution,[],[f42,f824,f3957,f67])).

fof(f3957,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK3,sK8(k6_funct_2(sK0,sK1,sK2,sK3),k6_funct_2(sK0,sK1,sK2,sK4))),k1_zfmisc_1(sK1))
    | ~ spl10_109 ),
    inference(avatar_component_clause,[],[f3956])).

fof(f1407,plain,
    ( spl10_6
    | ~ spl10_3
    | ~ spl10_15
    | ~ spl10_17
    | spl10_4
    | spl10_40
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f692,f629,f1405,f459,f641,f635,f453,f465])).

fof(f465,plain,
    ( spl10_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f453,plain,
    ( spl10_3
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f635,plain,
    ( spl10_15
  <=> ~ v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f641,plain,
    ( spl10_17
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f459,plain,
    ( spl10_4
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f629,plain,
    ( spl10_12
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
        | r2_hidden(k8_relset_1(sK0,sK1,sK2,X1),k6_funct_2(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f692,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X3),k6_funct_2(sK0,sK1,sK2,X4))
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X3,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK1)))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | v1_xboole_0(sK0) )
    | ~ spl10_12 ),
    inference(duplicate_literal_removal,[],[f690])).

fof(f690,plain,
    ( ! [X4,X3] :
        ( r2_hidden(k8_relset_1(sK0,sK1,sK2,X3),k6_funct_2(sK0,sK1,sK2,X4))
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X3,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK1)))
        | v1_xboole_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(sK1)))
        | v1_xboole_0(sK0) )
    | ~ spl10_12 ),
    inference(resolution,[],[f630,f51])).

fof(f630,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
        | r2_hidden(k8_relset_1(sK0,sK1,sK2,X1),k6_funct_2(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1))) )
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f629])).

fof(f651,plain,(
    spl10_17 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl10_17 ),
    inference(unit_resulting_resolution,[],[f46,f642])).

fof(f642,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f641])).

fof(f647,plain,(
    spl10_15 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | ~ spl10_15 ),
    inference(unit_resulting_resolution,[],[f47,f636])).

fof(f636,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f635])).

fof(f643,plain,
    ( spl10_6
    | spl10_12
    | ~ spl10_3
    | ~ spl10_15
    | ~ spl10_17
    | spl10_4 ),
    inference(avatar_split_clause,[],[f132,f459,f641,f635,f453,f629,f465])).

fof(f132,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK1)))
      | ~ m1_subset_1(k6_funct_2(sK0,sK1,sK2,X0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | v1_xboole_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | ~ r2_hidden(X1,X0)
      | r2_hidden(k8_relset_1(sK0,sK1,sK2,X1),k6_funct_2(sK0,sK1,sK2,X0)) ) ),
    inference(resolution,[],[f114,f76])).

fof(f76,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k8_relset_1(X0,X1,X2,X6),k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(k6_funct_2(X0,X1,X2,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ r2_hidden(X6,X3)
      | r2_hidden(k8_relset_1(X0,X1,X2,X6),k6_funct_2(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k8_relset_1(X0,X1,X2,X6),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ r2_hidden(X6,X3)
      | r2_hidden(k8_relset_1(X0,X1,X2,X6),X4)
      | k6_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
      | ~ r2_hidden(X6,X3)
      | k8_relset_1(X0,X1,X2,X6) != X5
      | r2_hidden(X5,X4)
      | k6_funct_2(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,(
    ! [X0] : m1_subset_1(k8_relset_1(sK0,sK1,sK2,X0),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t179_funct_2.p',dt_k8_relset_1)).

fof(f536,plain,(
    ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f86,f466,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t179_funct_2.p',t7_boole)).

fof(f466,plain,
    ( v1_xboole_0(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f465])).

fof(f86,plain,(
    r2_hidden(sK9(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f70,f50,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t179_funct_2.p',t2_subset)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t179_funct_2.p',existence_m1_subset_1)).

fof(f504,plain,(
    ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f484])).

fof(f484,plain,
    ( $false
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f84,f460,f72])).

fof(f460,plain,
    ( v1_xboole_0(sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f459])).

fof(f84,plain,(
    r2_hidden(sK9(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f70,f49,f68])).

fof(f477,plain,(
    spl10_3 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f115,f454,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t179_funct_2.p',t3_subset)).

fof(f454,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f453])).

fof(f115,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
