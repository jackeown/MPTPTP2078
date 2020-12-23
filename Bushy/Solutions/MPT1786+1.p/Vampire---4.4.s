%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t101_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:02 EDT 2019

% Result     : Theorem 56.99s
% Output     : Refutation 56.99s
% Verified   : 
% Statistics : Number of formulae       :  244 (2790 expanded)
%              Number of leaves         :   32 (1105 expanded)
%              Depth                    :   34
%              Number of atoms          :  985 (22803 expanded)
%              Number of equality atoms :  102 ( 681 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219994,plain,(
    $false ),
    inference(subsumption_resolution,[],[f219993,f168674])).

fof(f168674,plain,(
    r2_hidden(k3_xboole_0(sK2,sK9(sK3,sK0,sK1)),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f168673,f166])).

fof(f166,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',commutativity_k3_xboole_0)).

fof(f168673,plain,(
    r2_hidden(k3_xboole_0(sK9(sK3,sK0,sK1),sK2),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f168628,f657])).

fof(f657,plain,(
    m1_subset_1(sK9(sK3,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f656,f126])).

fof(f126,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,
    ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k5_tmap_1(sK0,sK1))
      | ~ r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k5_tmap_1(sK0,sK1)) )
    & r2_hidden(sK3,a_2_1_tmap_1(sK0,sK1))
    & r2_hidden(sK2,u1_pre_topc(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f55,f99,f98,f97,f96])).

fof(f96,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1))
                      | ~ r2_hidden(k4_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1)) )
                    & r2_hidden(X3,a_2_1_tmap_1(X0,X1))
                    & r2_hidden(X2,u1_pre_topc(X0))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),X2,X3),k5_tmap_1(sK0,X1))
                    | ~ r2_hidden(k4_subset_1(u1_struct_0(sK0),X2,X3),k5_tmap_1(sK0,X1)) )
                  & r2_hidden(X3,a_2_1_tmap_1(sK0,X1))
                  & r2_hidden(X2,u1_pre_topc(sK0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1))
                    | ~ r2_hidden(k4_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1)) )
                  & r2_hidden(X3,a_2_1_tmap_1(X0,X1))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,sK1))
                  | ~ r2_hidden(k4_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,sK1)) )
                & r2_hidden(X3,a_2_1_tmap_1(X0,sK1))
                & r2_hidden(X2,u1_pre_topc(X0))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1))
                | ~ r2_hidden(k4_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1)) )
              & r2_hidden(X3,a_2_1_tmap_1(X0,X1))
              & r2_hidden(X2,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK2,X3),k5_tmap_1(X0,X1))
              | ~ r2_hidden(k4_subset_1(u1_struct_0(X0),sK2,X3),k5_tmap_1(X0,X1)) )
            & r2_hidden(X3,a_2_1_tmap_1(X0,X1))
            & r2_hidden(sK2,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1))
            | ~ r2_hidden(k4_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1)) )
          & r2_hidden(X3,a_2_1_tmap_1(X0,X1))
          & r2_hidden(X2,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X2,sK3),k5_tmap_1(X0,X1))
          | ~ r2_hidden(k4_subset_1(u1_struct_0(X0),X2,sK3),k5_tmap_1(X0,X1)) )
        & r2_hidden(sK3,a_2_1_tmap_1(X0,X1))
        & r2_hidden(X2,u1_pre_topc(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1))
                    | ~ r2_hidden(k4_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1)) )
                  & r2_hidden(X3,a_2_1_tmap_1(X0,X1))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1))
                    | ~ r2_hidden(k4_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1)) )
                  & r2_hidden(X3,a_2_1_tmap_1(X0,X1))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r2_hidden(X3,a_2_1_tmap_1(X0,X1))
                        & r2_hidden(X2,u1_pre_topc(X0)) )
                     => ( r2_hidden(k9_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1))
                        & r2_hidden(k4_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X3,a_2_1_tmap_1(X0,X1))
                      & r2_hidden(X2,u1_pre_topc(X0)) )
                   => ( r2_hidden(k9_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1))
                      & r2_hidden(k4_subset_1(u1_struct_0(X0),X2,X3),k5_tmap_1(X0,X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t101_tmap_1)).

fof(f656,plain,
    ( m1_subset_1(sK9(sK3,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f655,f127])).

fof(f127,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f100])).

fof(f655,plain,
    ( m1_subset_1(sK9(sK3,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f654,f128])).

fof(f128,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f100])).

fof(f654,plain,
    ( m1_subset_1(sK9(sK3,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f645,f129])).

fof(f129,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f100])).

fof(f645,plain,
    ( m1_subset_1(sK9(sK3,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f133,f184])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,u1_pre_topc(X1))
              | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r2_hidden(sK9(X0,X1,X2),u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),sK9(X0,X1,X2),X2) = X0
            & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f115,f116])).

fof(f116,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,u1_pre_topc(X1))
          & k9_subset_1(u1_struct_0(X1),X4,X2) = X0
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(sK9(X0,X1,X2),u1_pre_topc(X1))
        & k9_subset_1(u1_struct_0(X1),sK9(X0,X1,X2),X2) = X0
        & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f115,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,u1_pre_topc(X1))
              | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,u1_pre_topc(X1))
              & k9_subset_1(u1_struct_0(X1),X4,X2) = X0
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f114])).

fof(f114,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,u1_pre_topc(X1))
              | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,u1_pre_topc(X1))
              & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,u1_pre_topc(X1))
            & k9_subset_1(u1_struct_0(X1),X3,X2) = X0
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',fraenkel_a_2_1_tmap_1)).

fof(f133,plain,(
    r2_hidden(sK3,a_2_1_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f100])).

fof(f168628,plain,
    ( r2_hidden(k3_xboole_0(sK9(sK3,sK0,sK1),sK2),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK9(sK3,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f162261,f541])).

fof(f541,plain,(
    ! [X4] :
      ( r2_hidden(k3_xboole_0(X4,sK2),a_2_1_tmap_1(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f538,f317])).

fof(f317,plain,(
    ! [X4] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,X4),a_2_1_tmap_1(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f316,f126])).

fof(f316,plain,(
    ! [X4] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,X4),a_2_1_tmap_1(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f315,f127])).

fof(f315,plain,(
    ! [X4] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,X4),a_2_1_tmap_1(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f314,f128])).

fof(f314,plain,(
    ! [X4] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,X4),a_2_1_tmap_1(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f297,f130])).

fof(f130,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f100])).

fof(f297,plain,(
    ! [X4] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,X4),a_2_1_tmap_1(sK0,X4))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f132,f202])).

fof(f202,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X1),X3,X2),a_2_1_tmap_1(X1,X2))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f187])).

fof(f187,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | k9_subset_1(u1_struct_0(X1),X3,X2) != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f132,plain,(
    r2_hidden(sK2,u1_pre_topc(sK0)) ),
    inference(cnf_transformation,[],[f100])).

fof(f538,plain,(
    ! [X21] : k9_subset_1(u1_struct_0(sK0),sK2,X21) = k3_xboole_0(X21,sK2) ),
    inference(forward_demodulation,[],[f477,f476])).

fof(f476,plain,(
    ! [X20] : k9_subset_1(u1_struct_0(sK0),X20,sK2) = k3_xboole_0(X20,sK2) ),
    inference(resolution,[],[f130,f182])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',redefinition_k9_subset_1)).

fof(f477,plain,(
    ! [X21] : k9_subset_1(u1_struct_0(sK0),X21,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X21) ),
    inference(resolution,[],[f130,f183])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',commutativity_k9_subset_1)).

fof(f162261,plain,(
    ! [X83] :
      ( ~ r2_hidden(X83,a_2_1_tmap_1(sK0,sK9(sK3,sK0,sK1)))
      | r2_hidden(X83,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f62896,f665])).

fof(f665,plain,(
    r2_hidden(sK9(sK3,sK0,sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f664,f126])).

fof(f664,plain,
    ( r2_hidden(sK9(sK3,sK0,sK1),u1_pre_topc(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f663,f127])).

fof(f663,plain,
    ( r2_hidden(sK9(sK3,sK0,sK1),u1_pre_topc(sK0))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f662,f128])).

fof(f662,plain,
    ( r2_hidden(sK9(sK3,sK0,sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f647,f129])).

fof(f647,plain,
    ( r2_hidden(sK9(sK3,sK0,sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f133,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),u1_pre_topc(X1))
      | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f62896,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X16,u1_pre_topc(sK0))
      | r2_hidden(X15,u1_pre_topc(sK0))
      | ~ r2_hidden(X15,a_2_1_tmap_1(sK0,X16)) ) ),
    inference(subsumption_resolution,[],[f62895,f5198])).

fof(f5198,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,u1_pre_topc(sK0))
      | m1_subset_1(sK9(X7,sK0,X6),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X7,a_2_1_tmap_1(sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f5197,f126])).

fof(f5197,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,u1_pre_topc(sK0))
      | m1_subset_1(sK9(X7,sK0,X6),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X7,a_2_1_tmap_1(sK0,X6))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f5196,f127])).

fof(f5196,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,u1_pre_topc(sK0))
      | m1_subset_1(sK9(X7,sK0,X6),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X7,a_2_1_tmap_1(sK0,X6))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f5145,f128])).

fof(f5145,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,u1_pre_topc(sK0))
      | m1_subset_1(sK9(X7,sK0,X6),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X7,a_2_1_tmap_1(sK0,X6))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f880,f184])).

fof(f880,plain,(
    ! [X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X4,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f262,f194])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t4_subset)).

fof(f262,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f128,f141])).

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',dt_u1_pre_topc)).

fof(f62895,plain,(
    ! [X15,X16] :
      ( r2_hidden(X15,u1_pre_topc(sK0))
      | ~ r2_hidden(X16,u1_pre_topc(sK0))
      | ~ m1_subset_1(sK9(X15,sK0,X16),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X15,a_2_1_tmap_1(sK0,X16)) ) ),
    inference(subsumption_resolution,[],[f62894,f880])).

fof(f62894,plain,(
    ! [X15,X16] :
      ( r2_hidden(X15,u1_pre_topc(sK0))
      | ~ r2_hidden(X16,u1_pre_topc(sK0))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK9(X15,sK0,X16),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X15,a_2_1_tmap_1(sK0,X16)) ) ),
    inference(subsumption_resolution,[],[f62893,f5204])).

fof(f5204,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,u1_pre_topc(sK0))
      | r2_hidden(sK9(X11,sK0,X10),u1_pre_topc(sK0))
      | ~ r2_hidden(X11,a_2_1_tmap_1(sK0,X10)) ) ),
    inference(subsumption_resolution,[],[f5203,f126])).

fof(f5203,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,u1_pre_topc(sK0))
      | r2_hidden(sK9(X11,sK0,X10),u1_pre_topc(sK0))
      | ~ r2_hidden(X11,a_2_1_tmap_1(sK0,X10))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f5202,f127])).

fof(f5202,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,u1_pre_topc(sK0))
      | r2_hidden(sK9(X11,sK0,X10),u1_pre_topc(sK0))
      | ~ r2_hidden(X11,a_2_1_tmap_1(sK0,X10))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f5147,f128])).

fof(f5147,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,u1_pre_topc(sK0))
      | r2_hidden(sK9(X11,sK0,X10),u1_pre_topc(sK0))
      | ~ r2_hidden(X11,a_2_1_tmap_1(sK0,X10))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f880,f186])).

fof(f62893,plain,(
    ! [X15,X16] :
      ( r2_hidden(X15,u1_pre_topc(sK0))
      | ~ r2_hidden(X16,u1_pre_topc(sK0))
      | ~ r2_hidden(sK9(X15,sK0,X16),u1_pre_topc(sK0))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK9(X15,sK0,X16),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X15,a_2_1_tmap_1(sK0,X16)) ) ),
    inference(subsumption_resolution,[],[f62892,f126])).

fof(f62892,plain,(
    ! [X15,X16] :
      ( r2_hidden(X15,u1_pre_topc(sK0))
      | ~ r2_hidden(X16,u1_pre_topc(sK0))
      | ~ r2_hidden(sK9(X15,sK0,X16),u1_pre_topc(sK0))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK9(X15,sK0,X16),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X15,a_2_1_tmap_1(sK0,X16))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f62891,f127])).

fof(f62891,plain,(
    ! [X15,X16] :
      ( r2_hidden(X15,u1_pre_topc(sK0))
      | ~ r2_hidden(X16,u1_pre_topc(sK0))
      | ~ r2_hidden(sK9(X15,sK0,X16),u1_pre_topc(sK0))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK9(X15,sK0,X16),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X15,a_2_1_tmap_1(sK0,X16))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f62840,f128])).

fof(f62840,plain,(
    ! [X15,X16] :
      ( r2_hidden(X15,u1_pre_topc(sK0))
      | ~ r2_hidden(X16,u1_pre_topc(sK0))
      | ~ r2_hidden(sK9(X15,sK0,X16),u1_pre_topc(sK0))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK9(X15,sK0,X16),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X15,a_2_1_tmap_1(sK0,X16))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f62828])).

fof(f62828,plain,(
    ! [X15,X16] :
      ( r2_hidden(X15,u1_pre_topc(sK0))
      | ~ r2_hidden(X16,u1_pre_topc(sK0))
      | ~ r2_hidden(sK9(X15,sK0,X16),u1_pre_topc(sK0))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK9(X15,sK0,X16),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X15,a_2_1_tmap_1(sK0,X16))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f259,f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X1),sK9(X0,X1,X2),X2) = X0
      | ~ r2_hidden(X0,a_2_1_tmap_1(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f259,plain,(
    ! [X2,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),u1_pre_topc(sK0))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | ~ r2_hidden(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f243,f128])).

fof(f243,plain,(
    ! [X2,X1] :
      ( r2_hidden(k9_subset_1(u1_struct_0(sK0),X1,X2),u1_pre_topc(sK0))
      | ~ r2_hidden(X2,u1_pre_topc(sK0))
      | ~ r2_hidden(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f127,f144])).

fof(f144,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
      | ~ r2_hidden(X5,u1_pre_topc(X0))
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),sK5(X0)),u1_pre_topc(X0))
            & r2_hidden(sK5(X0),u1_pre_topc(X0))
            & r2_hidden(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0))
            & r1_tarski(sK6(X0),u1_pre_topc(X0))
            & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f103,f106,f105,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK4(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f105,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,sK5(X0)),u1_pre_topc(X0))
        & r2_hidden(sK5(X0),u1_pre_topc(X0))
        & r2_hidden(X1,u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f106,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK6(X0)),u1_pre_topc(X0))
        & r1_tarski(sK6(X0),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f103,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
                ( ! [X2] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                    | ~ r2_hidden(X2,u1_pre_topc(X0))
                    | ~ r2_hidden(X1,u1_pre_topc(X0))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
                ( ! [X2] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                    | ~ r2_hidden(X2,u1_pre_topc(X0))
                    | ~ r2_hidden(X1,u1_pre_topc(X0))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',d1_pre_topc)).

fof(f219993,plain,(
    ~ r2_hidden(k3_xboole_0(sK2,sK9(sK3,sK0,sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f219980,f72128])).

fof(f72128,plain,(
    ~ r2_hidden(k3_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f72126,f168])).

fof(f168,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t1_subset)).

fof(f72126,plain,(
    ~ m1_subset_1(k3_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f72024,f68247])).

fof(f68247,plain,(
    m1_subset_1(k2_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f68108,f168])).

fof(f68108,plain,(
    r2_hidden(k2_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f68107,f29987])).

fof(f29987,plain,(
    k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f482,f131])).

fof(f131,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f100])).

fof(f482,plain,(
    ! [X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK2,X26) = k2_xboole_0(sK2,X26) ) ),
    inference(resolution,[],[f130,f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',redefinition_k4_subset_1)).

fof(f68107,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f68106,f394])).

fof(f394,plain,(
    k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f393,f126])).

fof(f393,plain,
    ( k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f392,f127])).

fof(f392,plain,
    ( k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f358,f128])).

fof(f358,plain,
    ( k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f129,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',d8_tmap_1)).

fof(f68106,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,sK3),a_2_0_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f68105,f129])).

fof(f68105,plain,
    ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,sK3),a_2_0_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f68104,f657])).

fof(f68104,plain,
    ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,sK3),a_2_0_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK9(sK3,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f67969,f665])).

fof(f67969,plain,
    ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,sK3),a_2_0_tmap_1(sK0,sK1))
    | ~ r2_hidden(sK9(sK3,sK0,sK1),u1_pre_topc(sK0))
    | ~ m1_subset_1(sK9(sK3,sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f309,f661])).

fof(f661,plain,(
    k9_subset_1(u1_struct_0(sK0),sK9(sK3,sK0,sK1),sK1) = sK3 ),
    inference(subsumption_resolution,[],[f660,f126])).

fof(f660,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK9(sK3,sK0,sK1),sK1) = sK3
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f659,f127])).

fof(f659,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK9(sK3,sK0,sK1),sK1) = sK3
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f658,f128])).

fof(f658,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK9(sK3,sK0,sK1),sK1) = sK3
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f646,f129])).

fof(f646,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK9(sK3,sK0,sK1),sK1) = sK3
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f133,f185])).

fof(f309,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,k9_subset_1(u1_struct_0(sK0),X0,X1)),a_2_0_tmap_1(sK0,X1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f308,f126])).

fof(f308,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,k9_subset_1(u1_struct_0(sK0),X0,X1)),a_2_0_tmap_1(sK0,X1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f307,f127])).

fof(f307,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,k9_subset_1(u1_struct_0(sK0),X0,X1)),a_2_0_tmap_1(sK0,X1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f306,f128])).

fof(f306,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,k9_subset_1(u1_struct_0(sK0),X0,X1)),a_2_0_tmap_1(sK0,X1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f295,f130])).

fof(f295,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,k9_subset_1(u1_struct_0(sK0),X0,X1)),a_2_0_tmap_1(sK0,X1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f132,f203])).

fof(f203,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)),a_2_0_tmap_1(X1,X2))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f193])).

fof(f193,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ( r2_hidden(sK11(X0,X1,X2),u1_pre_topc(X1))
            & r2_hidden(sK10(X0,X1,X2),u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),sK10(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK11(X0,X1,X2),X2)) = X0
            & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f119,f120])).

fof(f120,plain,(
    ! [X2,X1,X0] :
      ( ? [X5,X6] :
          ( r2_hidden(X6,u1_pre_topc(X1))
          & r2_hidden(X5,u1_pre_topc(X1))
          & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( r2_hidden(sK11(X0,X1,X2),u1_pre_topc(X1))
        & r2_hidden(sK10(X0,X1,X2),u1_pre_topc(X1))
        & k4_subset_1(u1_struct_0(X1),sK10(X0,X1,X2),k9_subset_1(u1_struct_0(X1),sK11(X0,X1,X2),X2)) = X0
        & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
        & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f119,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X5,X6] :
              ( r2_hidden(X6,u1_pre_topc(X1))
              & r2_hidden(X5,u1_pre_topc(X1))
              & k4_subset_1(u1_struct_0(X1),X5,k9_subset_1(u1_struct_0(X1),X6,X2)) = X0
              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
              & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f118])).

fof(f118,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
          | ! [X3,X4] :
              ( ~ r2_hidden(X4,u1_pre_topc(X1))
              | ~ r2_hidden(X3,u1_pre_topc(X1))
              | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
        & ( ? [X3,X4] :
              ( r2_hidden(X4,u1_pre_topc(X1))
              & r2_hidden(X3,u1_pre_topc(X1))
              & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',fraenkel_a_2_0_tmap_1)).

fof(f72024,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f68260,f30026])).

fof(f30026,plain,
    ( ~ r2_hidden(k3_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f29987,f952])).

fof(f952,plain,
    ( ~ r2_hidden(k3_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f950,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t7_boole)).

fof(f950,plain,
    ( ~ r2_hidden(k3_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1))
    | v1_xboole_0(k5_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f543,f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t2_subset)).

fof(f543,plain,
    ( ~ r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k5_tmap_1(sK0,sK1))
    | ~ r2_hidden(k3_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f539,f166])).

fof(f539,plain,
    ( ~ r2_hidden(k3_xboole_0(sK3,sK2),k5_tmap_1(sK0,sK1))
    | ~ r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f538,f134])).

fof(f134,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k5_tmap_1(sK0,sK1))
    | ~ r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k5_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f100])).

fof(f68260,plain,(
    ! [X0] :
      ( r2_hidden(X0,k5_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k5_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f68248,f169])).

fof(f68248,plain,(
    ~ v1_xboole_0(k5_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f68108,f178])).

fof(f219980,plain,
    ( r2_hidden(k3_xboole_0(sK2,sK3),k5_tmap_1(sK0,sK1))
    | ~ r2_hidden(k3_xboole_0(sK2,sK9(sK3,sK0,sK1)),u1_pre_topc(sK0)) ),
    inference(superposition,[],[f219450,f127272])).

fof(f127272,plain,(
    k3_xboole_0(sK2,sK3) = k3_xboole_0(sK1,k3_xboole_0(sK2,sK9(sK3,sK0,sK1))) ),
    inference(superposition,[],[f113380,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t16_xboole_1)).

fof(f113380,plain,(
    k3_xboole_0(sK2,sK3) = k3_xboole_0(k3_xboole_0(sK1,sK2),sK9(sK3,sK0,sK1)) ),
    inference(forward_demodulation,[],[f113306,f67368])).

fof(f67368,plain,(
    k3_xboole_0(sK2,sK3) = k3_xboole_0(sK3,sK9(k3_xboole_0(sK1,sK2),sK0,sK1)) ),
    inference(forward_demodulation,[],[f67367,f166])).

fof(f67367,plain,(
    k3_xboole_0(sK3,sK2) = k3_xboole_0(sK3,sK9(k3_xboole_0(sK1,sK2),sK0,sK1)) ),
    inference(forward_demodulation,[],[f67074,f4743])).

fof(f4743,plain,(
    ! [X1] : k3_xboole_0(sK3,X1) = k3_xboole_0(sK9(sK3,sK0,sK1),k3_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f179,f4702])).

fof(f4702,plain,(
    k3_xboole_0(sK9(sK3,sK0,sK1),sK1) = sK3 ),
    inference(superposition,[],[f661,f376])).

fof(f376,plain,(
    ! [X20] : k9_subset_1(u1_struct_0(sK0),X20,sK1) = k3_xboole_0(X20,sK1) ),
    inference(resolution,[],[f129,f182])).

fof(f67074,plain,(
    k3_xboole_0(sK3,sK9(k3_xboole_0(sK1,sK2),sK0,sK1)) = k3_xboole_0(sK9(sK3,sK0,sK1),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f4743,f17743])).

fof(f17743,plain,(
    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK9(k3_xboole_0(sK1,sK2),sK0,sK1)) ),
    inference(subsumption_resolution,[],[f17730,f129])).

fof(f17730,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,sK9(k3_xboole_0(sK1,sK2),sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f449,f541])).

fof(f449,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,a_2_1_tmap_1(sK0,sK1))
      | k3_xboole_0(sK1,sK9(X3,sK0,sK1)) = X3 ) ),
    inference(forward_demodulation,[],[f447,f166])).

fof(f447,plain,(
    ! [X3] :
      ( k3_xboole_0(sK9(X3,sK0,sK1),sK1) = X3
      | ~ r2_hidden(X3,a_2_1_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f376,f403])).

fof(f403,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK9(X3,sK0,sK1),sK1) = X3
      | ~ r2_hidden(X3,a_2_1_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f402,f126])).

fof(f402,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK9(X3,sK0,sK1),sK1) = X3
      | ~ r2_hidden(X3,a_2_1_tmap_1(sK0,sK1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f401,f127])).

fof(f401,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK9(X3,sK0,sK1),sK1) = X3
      | ~ r2_hidden(X3,a_2_1_tmap_1(sK0,sK1))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f361,f128])).

fof(f361,plain,(
    ! [X3] :
      ( k9_subset_1(u1_struct_0(sK0),sK9(X3,sK0,sK1),sK1) = X3
      | ~ r2_hidden(X3,a_2_1_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f129,f185])).

fof(f113306,plain,(
    k3_xboole_0(k3_xboole_0(sK1,sK2),sK9(sK3,sK0,sK1)) = k3_xboole_0(sK3,sK9(k3_xboole_0(sK1,sK2),sK0,sK1)) ),
    inference(superposition,[],[f67081,f17743])).

fof(f67081,plain,(
    ! [X1] : k3_xboole_0(sK3,X1) = k3_xboole_0(k3_xboole_0(sK1,X1),sK9(sK3,sK0,sK1)) ),
    inference(superposition,[],[f4743,f166])).

fof(f219450,plain,(
    ! [X0] :
      ( r2_hidden(k3_xboole_0(sK1,X0),k5_tmap_1(sK0,sK1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0)) ) ),
    inference(superposition,[],[f219313,f166])).

fof(f219313,plain,(
    ! [X0] :
      ( r2_hidden(k3_xboole_0(X0,sK1),k5_tmap_1(sK0,sK1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f219312,f880])).

fof(f219312,plain,(
    ! [X0] :
      ( r2_hidden(k3_xboole_0(X0,sK1),k5_tmap_1(sK0,sK1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f219311,f3208])).

fof(f3208,plain,(
    m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f443,f3202])).

fof(f3202,plain,(
    k3_xboole_0(o_0_0_xboole_0,sK1) = o_0_0_xboole_0 ),
    inference(resolution,[],[f3194,f135])).

fof(f135,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',dt_o_0_0_xboole_0)).

fof(f3194,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k3_xboole_0(X0,sK1) = X0 ) ),
    inference(superposition,[],[f3156,f139])).

fof(f139,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t6_boole)).

fof(f3156,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(superposition,[],[f376,f1189])).

fof(f1189,plain,(
    ! [X21] : k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X21) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f1101,f1180])).

fof(f1180,plain,(
    ! [X20] : k9_subset_1(u1_struct_0(sK0),X20,k1_xboole_0) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f1100,f137])).

fof(f137,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t2_boole)).

fof(f1100,plain,(
    ! [X20] : k9_subset_1(u1_struct_0(sK0),X20,k1_xboole_0) = k3_xboole_0(X20,k1_xboole_0) ),
    inference(resolution,[],[f1078,f182])).

fof(f1078,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f1074,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t3_subset)).

fof(f1074,plain,(
    r1_tarski(k1_xboole_0,u1_struct_0(sK0)) ),
    inference(superposition,[],[f1070,f137])).

fof(f1070,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f972,f166])).

fof(f972,plain,(
    ! [X35] : r1_tarski(k3_xboole_0(X35,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f443,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f1101,plain,(
    ! [X21] : k9_subset_1(u1_struct_0(sK0),X21,k1_xboole_0) = k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X21) ),
    inference(resolution,[],[f1078,f183])).

fof(f443,plain,(
    ! [X19] : m1_subset_1(k3_xboole_0(X19,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f376,f375])).

fof(f375,plain,(
    ! [X19] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X19,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f129,f181])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',dt_k9_subset_1)).

fof(f219311,plain,(
    ! [X0] :
      ( r2_hidden(k3_xboole_0(X0,sK1),k5_tmap_1(sK0,sK1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f219308,f9897])).

fof(f9897,plain,(
    r2_hidden(o_0_0_xboole_0,u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f9788,f260])).

fof(f260,plain,(
    r2_hidden(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f245,f128])).

fof(f245,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f127,f161])).

fof(f161,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t5_pre_topc)).

fof(f9788,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(superposition,[],[f9605,f137])).

fof(f9605,plain,(
    ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0 ),
    inference(superposition,[],[f9519,f166])).

fof(f9519,plain,(
    ! [X20] : k3_xboole_0(X20,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(backward_demodulation,[],[f9517,f3238])).

fof(f3238,plain,(
    ! [X20] : k9_subset_1(u1_struct_0(sK0),X20,o_0_0_xboole_0) = k3_xboole_0(X20,o_0_0_xboole_0) ),
    inference(resolution,[],[f3208,f182])).

fof(f9517,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(resolution,[],[f2326,f135])).

fof(f2326,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k9_subset_1(u1_struct_0(sK0),X1,X0) = X0 ) ),
    inference(superposition,[],[f1180,f139])).

fof(f219308,plain,(
    ! [X0] :
      ( r2_hidden(k3_xboole_0(X0,sK1),k5_tmap_1(sK0,sK1))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ r2_hidden(o_0_0_xboole_0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f444,f218304])).

fof(f218304,plain,(
    ! [X207] : k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,k3_xboole_0(X207,sK1)) = k3_xboole_0(X207,sK1) ),
    inference(resolution,[],[f10426,f443])).

fof(f10426,plain,(
    ! [X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,X26) = X26 ) ),
    inference(backward_demodulation,[],[f10421,f3244])).

fof(f3244,plain,(
    ! [X26] :
      ( k4_subset_1(u1_struct_0(sK0),o_0_0_xboole_0,X26) = k2_xboole_0(o_0_0_xboole_0,X26)
      | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f3208,f197])).

fof(f10421,plain,(
    ! [X1] : k2_xboole_0(o_0_0_xboole_0,X1) = X1 ),
    inference(superposition,[],[f9893,f165])).

fof(f165,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',commutativity_k2_xboole_0)).

fof(f9893,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f9788,f136])).

fof(f136,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t101_tmap_1.p',t1_boole)).

fof(f444,plain,(
    ! [X12,X13] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),X12,k3_xboole_0(X13,sK1)),k5_tmap_1(sK0,sK1))
      | ~ r2_hidden(X13,u1_pre_topc(sK0))
      | ~ r2_hidden(X12,u1_pre_topc(sK0))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f376,f436])).

fof(f436,plain,(
    ! [X12,X13] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),X12,k9_subset_1(u1_struct_0(sK0),X13,sK1)),k5_tmap_1(sK0,sK1))
      | ~ r2_hidden(X13,u1_pre_topc(sK0))
      | ~ r2_hidden(X12,u1_pre_topc(sK0))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f435,f394])).

fof(f435,plain,(
    ! [X12,X13] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),X12,k9_subset_1(u1_struct_0(sK0),X13,sK1)),a_2_0_tmap_1(sK0,sK1))
      | ~ r2_hidden(X13,u1_pre_topc(sK0))
      | ~ r2_hidden(X12,u1_pre_topc(sK0))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f434,f126])).

fof(f434,plain,(
    ! [X12,X13] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),X12,k9_subset_1(u1_struct_0(sK0),X13,sK1)),a_2_0_tmap_1(sK0,sK1))
      | ~ r2_hidden(X13,u1_pre_topc(sK0))
      | ~ r2_hidden(X12,u1_pre_topc(sK0))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f433,f127])).

fof(f433,plain,(
    ! [X12,X13] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),X12,k9_subset_1(u1_struct_0(sK0),X13,sK1)),a_2_0_tmap_1(sK0,sK1))
      | ~ r2_hidden(X13,u1_pre_topc(sK0))
      | ~ r2_hidden(X12,u1_pre_topc(sK0))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f370,f128])).

fof(f370,plain,(
    ! [X12,X13] :
      ( r2_hidden(k4_subset_1(u1_struct_0(sK0),X12,k9_subset_1(u1_struct_0(sK0),X13,sK1)),a_2_0_tmap_1(sK0,sK1))
      | ~ r2_hidden(X13,u1_pre_topc(sK0))
      | ~ r2_hidden(X12,u1_pre_topc(sK0))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f129,f203])).
%------------------------------------------------------------------------------
